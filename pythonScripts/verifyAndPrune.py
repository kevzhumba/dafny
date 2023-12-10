#This should loop through all files currently in libraries, perturb them, and then remove any that verify or can't be determined within some threshold

import sys
import pathlib
import os
import subprocess
import time
import random

#arg1 is the source directory for files. 

def isPerturbed(file):
    fileName = os.path.basename(file)  #gets the file name without directory
    return fileName.startswith("_")

def isAlreadyUnverified(file):
    return os.path.exists(file.with_suffix(".log"))
        

srcDir = sys.argv[1]
srcPath = pathlib.Path(srcDir)

allFilesAndDirs = list(filter(lambda x: not isPerturbed(x), srcPath.rglob("*.dfy"))) #get all files that are dafny
fileNameToCli = {}
for file in allFilesAndDirs:
    print("Trying to perturb file " + str(file))
    fileName = os.path.basename(file)
    f = open(file, "r")
    lines = f.readlines()
    possibleRunLines = list(filter(lambda x: ("RUN:" in x and "%verify" in x and "%s" in x and x.startswith("//")), lines))
    if (len(possibleRunLines) == 1):
        arguments = possibleRunLines[0].strip().split(" ")
        print(arguments)
        if ("%verify" in arguments and "\"%s\"" in arguments):
            start = arguments.index("%verify") + 1
            end = arguments.index("\"%s\"")
            commandArgs = arguments[start : end]
            fileNameToCli[str(file)] = commandArgs
        elif ("%verify" in arguments and "%s" in arguments):
            start = arguments.index("%verify") + 1
            end = arguments.index("%s")
            commandArgs = arguments[start : end]
            fileNameToCli[str(file)] = commandArgs
        else:
            fileNameToCli[str(file)] = []
    else:
        fileNameToCli[str(file)] = []
    if fileName.startswith("_"):
        continue
        
    #here we should try compiling first with time out
    # try:
    #     args = ["./Scripts/dafny", "verify"] + fileNameToCli[str(file)] + [file]
    #     print(str(args))
    #     a = subprocess.run(args, timeout=120, capture_output=True)
    #     if (a.returncode == 0):
    #         #verified correctly
    #         try:
    #             b = subprocess.run(["./Scripts/dafny", "verify"] + fileNameToCli[str(file)] + ["--perturbed"] + [file], capture_output=True , timeout=120)
    #         except:
    #             print("Something went wrong when perturbing")
    #     elif (a.returncode == 4):
    #         print(str(file) + " did not verify correctly")
    #     elif (a.returncode == 1):
    #         updatedArgs = ["./Scripts/dafny", "verify"] + [file]
    #         fileNameToCli[str(file)] = []
    #         a = subprocess.run(updatedArgs, timeout=120, capture_output=True)
    #         if (a.returncode == 0):
    #             #verified correctly
    #             try:
    #                 b = subprocess.run(["./Scripts/dafny", "verify"] + fileNameToCli[str(file)] + ["--perturbed"] + [file], capture_output = True, timeout=120)
    #             except:
    #                 print("Something went wrong when perturbing")
    #         else:
    #             print("Something went wrong")
    #     else:
    #         print("Something wrong happened when parsing or resolving file " + str(file))
    #         print(a.stdout)
    #         print(a.stderr)
    # except subprocess.TimeoutExpired: #if timeout just skip the file
    #     print("Timed out when analyzing the file " + str(file))
    # except:
    #     print("Something went wrong when analyzing file " + str(file))

# now we have perturbed everything, prune the ones that actually verify
allPerturbedFilesAndDirs = list(filter(lambda x:  isPerturbed(x) and not isAlreadyUnverified(x), srcPath.rglob("*.dfy")))
random.shuffle(allPerturbedFilesAndDirs)

numInDataset = 0
count = 0 
for file in allPerturbedFilesAndDirs:
    if (numInDataset > len(allPerturbedFilesAndDirs)/10):
        break
    print("verifying file " + str(count) + " out of " + str(len(allPerturbedFilesAndDirs))  + " "+ str(file))
    count = count + 1

    fileName = os.path.basename(file)  #gets the file name without directory
    if not (fileName.startswith("_")):
        continue
    #perturbed files start with _
    end = fileName.rindex("_")
    nameInDict = str(os.path.join(os.path.dirname(file), fileName[1: end] + ".dfy"))
    cliArgs = fileNameToCli[nameInDict]
    try:
        args = ["./Scripts/dafny", "verify"] + cliArgs + [file]
        a = subprocess.run(args, timeout=120, capture_output=True)
        if (a.returncode != 4):
            os.remove(file)
        else:
            verifierOutputName = file.with_suffix(".log")
            f = open(verifierOutputName, "wb")
            f.write(a.stdout)
            f.close()
            numInDataset += 1
    except subprocess.TimeoutExpired:
        os.remove(file)
    except Exception as e:
        print("Some exception occurred when verifiying perturbed")
        print(e)



        




