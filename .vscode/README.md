# VS Code settings for working with the SPARK toolset

This README explains how to set up and work with the components of the SPARK
toolset in VS Code.

## Ada & SPARK VS Code extension

Installing the
[Ada & SPARK](https://marketplace.visualstudio.com/items?itemName=AdaCore.ada)
VS Code extension is recommended.

## Settings Precedence

VS Code merges settings in the following order (last one wins on conflicts):

1. VS Code default settings
2. User settings (`$HOME/.config/Code/User/settings.json`)
3. Workspace settings (`.code-workspace`)
4. Folder settings (`.vscode/settings.json` within a project folder)

> Note that settings in the `.vscode/settings.json` apply for the whole folder
> hierarchy are not overridable neither by a workspace (`.code-workspace`) file
> nor by a lower level `.vscode/settings.json` file. Therefore it is
> recommended to put only the minimal globally applicable settings in this
> file.
>
> Conversely, different workspace (`.code-workspace`) files can be defined and
> explicitly selected in VS Code. The location where they are stored does not
> matter. However, paths in the workspace file must be **relative to the
> location of that file**. More on that below.

## Repository structure

The following graph illustrates the folder hierarchy of the SPARK toolset
components from the viewpoint of the development environment.

```
spark2014/                # Top-level folder. Holds also the configuration for
|                         # building the `gnatprove` executable.
├── .vscode/
│   └── settings.json     # Shared VS Code settings for all subfolders.
│   └── x.code-workspace  # Customizable VS Code settings for working with
|                         # (sub-)project x.
|
├── gnat2why/             # Configuration for building the `gnat2why` executable.
├── gnat2why/gnat_src     # GNAT sources for the frontend part of `gnat2why`.
|                         # (Symlinked repository)
├── src/                  # Sources for `gnatprove` and the backend part of.
|                         # `gnat2why`.
├── why3/                 # Sources and configuration for building the `why3` and
|                         # `gnatwhy3` executables. (Git submodule)
|
├── testsuite/            # Sources for `gnatprove` and `gnat2why`.
│   └── gnatprove
│       └── tests         # The core subset of tests.
│       └── sparklib      # Tests for SPARKlib. (Symlinked repository)
│       └── ...           # Dedicated testsuites and support resources.
```

## Workspace files

As seen above there are several executables that are implemented in Ada. The VS
Code Ada plugin expects a single top-level Ada project file for one workspace.
The solution is to define several
[VS Code Workspaces](https://code.visualstudio.com/docs/editor/multi-root-workspaces)
via workspace (`.code-workspace`) files. One for each project/executable.

A workspace file can be selected in VS Code from the menu: "File" > "Open
Workspace from File", or passed to VS Code when starting the tool.

> **Note:** The paths in the workspace file are resolved wrt. the location of
> the workspace file. So, the currently active directory doesn't matter.
>
> This works also when using
> [VS Code in the Remote Mode](https://code.visualstudio.com/docs/remote/remote-overview).
> Once the remote mode is set up and running simply open a workspace file from
> the remote host. In the remote mode it is easier to open the file from the VS
> Code menu.

For example, assuming that your working directory is at the root of the
`spark2014` repository in a local machine and you are on Linux you can run the
following commands:

### Example: Working on gnatprove

```
$ code .vscode/gnatprove.code-workspace &
```

### Example: Working on gnat2why

```
$ code .vscode/gnat2why.code-workspace &
```

### Example: Working on tests

This workspace has been provided for convenient browsing and searching in the
tests only. For most of the tests it is assumed that a `.gpr` file will be
generated on the fly by the test framework. And hence they cannot be directly
executed and verified in this workspace.

```
$ code .vscode/tests.code-workspace &
```

> **Note:** These example workspace definitions can be used as a starting point
> for developers to define their own workspace setups.
>
> For instance, the example workspaces only include source directories from
> within the `spark2014` repository. This means, e.g., that one cannot directly
> open files from dependent projects like `GNATCOLL` nor perform searches in
> them. It is, however, still possible navigate to their sources using
> cross-references and browse them this way in VS Code. This might be typically
> sufficient.
>
> When opening the workspace for the first time the Ada & SPARK VS Code
> extension displays the message "Some project source directories are not
> listed in your workspace: do you want to add them?". If the minimal set of
> source directories is sufficient one should choose "No".
>
> Conversely, if having the sources of some of these projects in the workspace
> is preferred, they can be added to the workspace by choosing "Yes" or editing
> the workspace file manually or via the "`Ada: Add Missing Source Directories
> to Workspace`" command in VS Code.
>
> A modified workspace definition should be stored in a local file outside the
> `spark2014` repository. If the workspace was modified interactively, then it
> is easiest to save it via the "File" > "Save Workspace As" menu in VS Code as
> this will take care of adjusting the paths according to the target location.
