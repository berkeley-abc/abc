### References

This method has been discussed in the following sources:

https://gist.github.com/0xjac/85097472043b697ab57ba1b1c7530274

https://medium.com/@bilalbayasut/github-how-to-make-a-fork-of-public-repository-private-6ee8cacaf9d3

https://stackoverflow.com/questions/10065526/github-how-to-make-a-fork-of-public-repository-private/30352360#30352360

### Steps

In the following steps, **this repository** refers to `git@github.com:NTU-ALComLab/LSV-PA.git`

1. [Import][GitHub Importer] this repository and set the new repository private.
- Name the new repository whatever you like. In this example we name it `LSV-PA-private`.

[GitHub Importer]: https://docs.github.com/en/free-pro-team@latest/github/importing-your-projects-to-github/importing-a-repository-with-github-importer

2. Clone the private repository to your local machine.
```
~$ git clone git@github.com:<your-username>/LSV-PA-private.git
```

3. Add this repository as a remote in order to update your private repository.
```
~$ cd LSV-PA-private
~/LSV-PA-private$ git remote add upstream git@github.com:NTU-ALComLab/LSV-PA.git
```

List all of your remotes by `git remote -v`.
```
origin	git@github.com:<your-username>/LSV-PA-private.git (fetch)
origin	git@github.com:<your-username>/LSV-PA-private.git (push)
upstream	git@github.com:NTU-ALComLab/LSV-PA.git (fetch)
upstream	git@github.com:NTU-ALComLab/LSV-PA.git (push)
```

Now you can update your private repository by `git fetch upstream`.
Note that you don't have the permission to push to this repository.
You can disable it by `git remote set-url --push upstream DISABLE`.

There is no need to create another branch in your private repository.
In the following we assume your code is developed in `master`.

4. To submit your code, first you have to create a branch named with your student ID number in your public fork.
```
~$ git clone git@github.com:<your-username>/LSV-PA.git LSV-PA-public-fork
~$ cd LSV-PA-public-fork
~/LSV-PA-public-fork$ git checkout -b <your-student-id>
```

Second, pull the code from the master branch of your private repository to the branch named with your student ID number.
```
~/LSV-PA-public-fork$ git remote add private git@github.com:<your-username>/LSV-PA-private.git
~/LSV-PA-public-fork$ git pull private master
```

Third, push your code to the public fork and send a pull request to this repository via GitHub UI.
```
~/LSV-PA-public-fork$ git push --set-upstream origin <your-student-id>
```

To repeat the process, you only need `git pull private master` and `git push`.
