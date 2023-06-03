#!/usr/bin/env python3

import os
import sys
from pathlib import Path
import subprocess

cache_dir = sys.argv[1]
src_paths = [Path(x) for x in sys.argv[2:]]

tgt_paths = [ p.parents[0] / (p.stem + ".lagda.tex") for p in src_paths ]
bak_paths = [ p.parents[0] / (p.name + ".bak") for p in src_paths ]

commands = []

for src_path, tgt_path in zip(src_paths, tgt_paths):
    with open(src_path, 'r') as f:
        src = f.read();

    tgt = ""
    prefixes = []
    mode = "none"
    stop_command_on_empty_line = False
    def start_command(name):
        global mode, tgt, prefixes
        for p in prefixes:
            name = p + name
        commands.append(name)
        if mode == "hide":
            tgt += "\\end{code}\n"
        elif mode == "command":
            print(f"ERROR: Line {line_num} starts a nested command:\n  {line}")
        mode = "command"
        tgt += "\\newcommand*\\" + name + "{\\begin{code}\n"
    def stop_command():
        global mode, tgt, prefixes
        tgt += "\\end{code}}\n"
        mode = "none"
    for line_num, line in enumerate(src.splitlines()):
        l = line.strip()
        if l.startswith("--!") or l.startswith("-- !"):
            l = l.split("!", 1)[1].strip()
            if "{" in l:
                name = l.split(" ", 1)[0]
                start_command(name)
            elif "}" in l:
                stop_command()
            elif ">" in l:
                prefixes.append(l.split(" ", 1)[0])
            elif "<" in l:
                prefixes.pop()
            else:
                name = l.split(" ", 1)[0]
                start_command(name)
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

    with open(tgt_path, 'w') as f:
        f.write(tgt)

print("Defined LaTeX-commands:")
for c in commands: 
    print("  \\" + c)

print("Renaming original files...")
for src_path, bak_path in zip(src_paths, bak_paths):
    src_path.rename(bak_path)

print("Running agda with latex backend...")
for tgt_path in tgt_paths:
    subprocess.run(["agda", "--latex", "--only-scope-checking", "--latex-dir=" + cache_dir, tgt_path])

print("Restoring original files...")
for src_path, bak_path in zip(src_paths, bak_paths):
    bak_path.rename(src_path)

print("Deleting .lagda.tex files...")
for tgt_path in tgt_paths:
    tgt_path.unlink()
