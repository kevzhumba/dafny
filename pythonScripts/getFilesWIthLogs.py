import sys
import pathlib
import os
import subprocess
import time
import random
def isPerturbed(file):
    fileName = os.path.basename(file)  #gets the file name without directory
    return fileName.startswith("_")

srcDir = sys.argv[1]
srcPath = pathlib.Path(srcDir)
allPerturbedFilesAndDirs = list(filter(lambda x:  isPerturbed(x), srcPath.rglob("*.dfy")))
#i think we should also remove any files that don't have a corresponding perturbed version
for file in allPerturbedFilesAndDirs:
    if not (os.path.exists(file.with_suffix(".log"))):
        os.remove(file) #we are going to remove any perturbed examples that don't have a log

allFiles = list(filter(lambda x: os.path.isfile(x), srcPath.rglob("*")))
allPerturbedFiles =  list(filter(lambda x:  isPerturbed(x), srcPath.rglob("*.dfy")))
print(len(allPerturbedFiles))

for file in allFiles:
    if not (os.path.basename(file).endswith(".dfy") or os.path.basename(file).endswith(".log")):
        os.remove(file)

allLogfiles = list(srcPath.rglob("*.log"))
for log in allLogfiles:
    with open(log, 'r') as fin:
        data = fin.read().splitlines(True)
    with open(log, 'w') as fout:
        if (data[0].lower().strip() == "not legacy result"):
            fout.writelines(data[1:])












