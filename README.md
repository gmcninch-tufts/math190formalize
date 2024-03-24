# Math 190 - Formalization of Mathematics

This repository contains Lean code for the class
[math190-Tufts](https://gmcninch-tufts.github.io/2024-Sp-Math190/).

The Lean files to be used in the class are in the folder
[Math190formalize](https://github.com/gmcninch-tufts/math190formalize/tree/main/Math190formalize).

## Using Gitpod

- You can run the code on the web - in your browser - using Gitpod. To
  get started, click this link:

  [![Open in Gitpod](https://gitpod.io/button/open-in-gitpod.svg)](https://gitpod.io/#https://github.com/gmcninch-tufts/math190formalize)

- You will be prompted to make an account, if you do not yet have one
  -- the free tier offers 50 hours of use per month.) This is the
  easiest way to get started if you have never used Lean before.  You
  can accept the default "New Workspace" options and hit the
  "continue" button. It will then take about five minutes to load up a
  new workspace and auto-install the Lean mathematical library (wait
  for all the "cloning", "building", "compiling", "downloading" and
  "decompressing" steps to finish).  The workspace you just created
  will be accessible later from your [Gitpod user
  page](https://gitpod.io/workspaces).

  **Note:** you can return to your workspace from your [gitpod landing
  page](https://gitpod.io/workspaces) (once you have an account). Your
  workspace will be saved for 2 weeks by default; if you *pin* the
  workspace, it'll be kept indefinitely. Clicking the [Open in Gitpod]
  button (above) will create a *new* workspace for you.

## Using *your computer*

  Alternatively, you can also [install
  Lean](https://leanprover-community.github.io/get_started.html) to
  your own computer, then clone this repository to your computer by
  typing 
  
  ```
  git clone git@github.com/gmcninch-tufts/math190formalize.git
  ``` 
  
  at the command line.  This will create a copy of the repository on
  your computer. 
  
  Now, assuming you have already installed Lean (see above), open a
  terminal, change directories to the repository you just cloned, and run the following:
  
  ```
  lake exe cache get
  ```
  
  This will install `mathlib` (and other stuff).
  
  Now, with a suitable *editor*, you can then interact with the code
  on your computer.
