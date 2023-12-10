import sys
import pathlib
import os
import csv
def isPerturbed(file):
    fileName = os.path.basename(file)  #gets the file name without directory
    return fileName.startswith("_")
srcDir = sys.argv[1]
srcPath = pathlib.Path(srcDir)
allPerturbedFilesAndDirs = list(filter(lambda x: isPerturbed(x), srcPath.rglob("*.dfy")))
fields = ['incorrect_program', 'verifier_output', 'correct_program']
filename = "dataset.csv"
with open(filename, 'w') as csvfile:
    csvwriter = csv.writer(csvfile)
    csvwriter.writerow(fields)
    for file in allPerturbedFilesAndDirs:
        logFile = file.with_suffix(".log")
        #get the original file
        perturbedFileName = os.path.basename(file)  #gets the file name without directory
        end = perturbedFileName.rindex("_")
        correctProgram = os.path.join(os.path.dirname(file), perturbedFileName[1: end] + ".dfy")

        with open(file, "r") as perturbedFile:
            with open(logFile, "r") as logFileOpen:
                with open(correctProgram, "r") as correctFile:
                    row = [perturbedFile.read(), logFileOpen.read(), correctFile.read()]
                    csvwriter.writerow(row)

        



