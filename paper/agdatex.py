#!/usr/bin/env python3

import os
import sys
from pathlib import Path
from argparse import ArgumentParser
import tempfile
import subprocess
import shutil


# Parse Arguments

ap = ArgumentParser(
    prog="agdatex",
    description="Extract LaTeX-Macros from .agda files guided by comment annotations",
)

ap.add_argument("-o", "--outputdir", metavar="PATH", default="latex",
                help="Output directory for agda's LaTeX backend. Forwarded as --latex-dir to agda. Default: 'latex'.")

ap.add_argument("-e", "--exportfile", metavar="PATH",
                help="This file will \\input all generated .tex files. Both .tex and .sty are supported. Default: 'OUTPUTDIR/agda-generated.sty'.")

ap.add_argument("-t", "--tempdir", metavar="PATH",
                help="Temporary directory to copy the project root to. Default: fresh system-dependent temporary dir.")

ap.add_argument("-k", "--keeptempdir", action='store_true',
                help="Keep temporary directory for debugging.")

ap.add_argument("-r", "--root", metavar="PATH",
                help="Project root. Default: Search for .git directory.")

ap.add_argument("-i", "--index", metavar="PATH",
                help="Write the list of generated macros to this file.")

ap.add_argument("sources", metavar="SRC_PATH", nargs="+",
                help="Path to an annotated .agda-file.")

args = ap.parse_args()


# Resolve Project Root

if args.root is not None:
    root = Path(args.root)
else:
    # Search for .git directory.
    root = Path(os.getcwd())
    found_git_dir = False
    while True:
        for p in root.iterdir():
            if p.is_dir() and p.name == ".git":
                found_git_dir = True
                break
        if found_git_dir or len(root.parents) == 0:
            break
        root = root.parents[0]
    if not found_git_dir:
        print("ERROR: No .git directory found and also no explicit --root specified.")
        sys.exit(1)

root = root.absolute()


# Check if sources are relative to project root

src_paths = []
for p in args.sources:
    try:
        src_paths.append(Path(p).absolute().relative_to(root))
    except ValueError as e:
        print(f"ERROR: Source path '{p}' is not relative to root '{root}'.")
        sys.exit(1)


# Create temporary directory

if args.tempdir is not None:
    tmp_root = Path(args.tempdir)
    tmp_root.mkdir(exist_ok=True)
else:
    tmp_root_obj = tempfile.TemporaryDirectory(prefix="agdatex")
    tmp_root = Path(tmp_root_obj.name)


# Copy project root to temporary directory

shutil.copytree(
    root,
    tmp_root,
    dirs_exist_ok=True,
    symlinks=True,
    ignore=shutil.ignore_patterns(tmp_root)
)


# Transpile .agda-sources to .lagda.tex-targets

tgt_paths = [ p.parents[0] / (p.stem + ".lagda.tex") for p in src_paths ]

commands = []

for src_path, tgt_path in zip(src_paths, tgt_paths):
    with open(tmp_root / src_path, 'r') as f:
        src = f.read();

    tgt = ""
    prefixes = []
    mode = "none"
    stop_command_on_empty_line = False
    def start_command(name, is_inline):
        global mode, tgt, prefixes
        for p in prefixes:
            name = p + name
        commands.append(name)
        if mode == "hide":
            tgt += "\\end{code}\n"
        elif mode == "command":
            print(f"ERROR: Line {line_num} starts a nested command:\n  {line}")
        mode = "command"
        opt = "[inline]" if is_inline else ""
        tgt += "\\newcommand*\\" + name + "{\\begin{code}" + opt + "\n"
    def stop_command():
        global mode, tgt, prefixes
        tgt += "\\end{code}}\n"
        mode = "none"
    for line_num, line in enumerate(src.splitlines()):
        l = line.strip()
        if l.startswith("--!") or l.startswith("-- !"):
            if mode == "command" and stop_command_on_empty_line:
                stop_command_on_empty_line = False
                stop_command()
            l = l.split("!", 1)[1].strip()

            is_inline = l[0] == "!"
            if is_inline:
                l = l[1:].strip()
            if "{" in l:
                name = l.split(" ", 1)[0]
                start_command(name, is_inline)
            elif "}" in l:
                stop_command()
            elif ">" in l:
                prefixes.append(l.split(" ", 1)[0])
            elif "<" in l:
                prefixes.pop()
            else:
                name = l.split(" ", 1)[0]
                start_command(name, is_inline)
                stop_command_on_empty_line = True
                # print(f"ERROR: Line {line_num} contains invalid agdatex command:\n  {line}")
        elif line.strip() == "":
            if mode == "command" and stop_command_on_empty_line:
                stop_command_on_empty_line = False
                stop_command()
            tgt += "\n"
        else:
            if mode == "none":
                tgt += "\\begin{code}[hide]\n"
                mode = "hide"
            tgt += line + "\n"
    if mode == "hide":
        tgt += "\\end{code}\n"
    if mode == "command" and stop_command_on_empty_line:
        stop_command_on_empty_line = False
        stop_command()

    with open(tmp_root / tgt_path, 'w') as f:
        f.write(tgt)


# Write generated LaTeX macros into a file, if --index was specified

if args.index is not None:
    s = ""
    for c in commands: 
        s += "\\" + c + "\n"
    with open(args.index, 'w') as f:
        f.write(s)

# print("Defined LaTeX-commands:")
# for c in commands: 
#     print("  \\" + c)


# Remove copies of the .agda-files, such that Agda will only see the .lagda.tex files.

for src_path in src_paths:
    (tmp_root / src_path).unlink()


# Run agda on the .lagda.tex files to generate .tex files.

output_dir = Path(args.outputdir)
output_dir.mkdir(exist_ok=True)

print("Running agda with latex backend...")
for tgt_path in tgt_paths:
    print(f"  Processing {tgt_path}...")
    subprocess.run(
        ["agda", "--latex", "--only-scope-checking", "--latex-dir=" + str(output_dir.absolute()), str(tgt_path)],
        cwd=tmp_root,
    )


# Create an export .tex-file which imports all generated .tex-files.

if args.exportfile is not None:
    export_file = Path(args.exportfile)
else:
    export_file = output_dir / "agda-generated.sty"

src_names = [ p.stem for p in src_paths ]
s = ""
if export_file.suffix == ".sty":
    s += "\ProvidesPackage{" + export_file.stem + "}\n"
for p in output_dir.glob("**/*.tex"):
    if p.stem in src_names:
        s += "\\input{" + str(p.relative_to(output_dir)) + "}\n"
with open(export_file, 'w') as f:
    f.write(s)


# Delete temporary directory

if args.tempdir is not None and not args.keeptempdir:
    shutil.rmtree(tmp_root)
