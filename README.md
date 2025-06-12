This is a github mirror of some files from the AutoSpec Artifact (https://doi.org/10.5281/zenodo.10912658)

It is updated up to the Version v1.0 (Apr 3, 2024).

The purpose of this is to have a git diff of my edits to run and compare against the tool.

To get the rest of the artifact:
```
wget https://zenodo.org/records/10912658/files/AutoSpec.zip
unzip AutoSpec.zip
```

And then replace the files within the downloaded zip with the ones here (if you want the changes I made for comparison):
```
rsync -av path/to/this/AutoSpec path/to/AutoSpec/from/the/zip 
```