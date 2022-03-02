---
visibility: PRIVATE
---

# TODO: Repo Initialization

- [X] Rename the directory `QN`, replacing `N` with the current quarter
- [X] Rename the directory `YYYY`, replacing `YYYY` with the current year
- [X] Make the following replacements in this file:
  - `$Clientname$` -> clients name
  - `$client-url$` -> client's home page
- [ ] Initialize the report skeleton
  ```sh
  cd YYYY/QN/report
  make init
  ```
- [ ] Add client artifacts to the `artifacts` subdirectory, using the instructions
  in the final section below.
- [ ] Remove this section
- [ ] Invite the client team members to this repo

# Partnership Workspace _of_ Informal Systems ⨯ Heliax

This repository is a workspace for [Informal Systems](https://informal.systems/)
and [Heliax](https://heliax.dev/) to collaborate on the system designed and developed
by Heliax in the course of the partnership.

## Usage and organization

The artifacts for each engagement are gathered in a subdirectory named
after the year and quarter in which the project was carried out.

These artifacts include:

- The artifacts generated the course of the project.
- The artifacts under review, referenced as git submodules.

### To clone just the artifacts Informal created during the audit

``` sh
git clone git@github.com:informalsystems/partnership-heliax.git
```

### To clone all artifacts, including Heliax's source code at the relevant commits

``` sh
git clone --recurse-submodules git@github.com:informalsystems/partnership-heliax.git
```


### To update the submodules if you've already cloned the repository

``` sh
git submodule init
git submodule update
```

### To add an artifact into an `artifacts` directory

```sh
git submodule add https://github.com/$CLIENT$/$PROJECT$
cd $PROJECT$
git checkout $TAG$
```

where $TAG$ is the tag or commit agreed to be under partnership.

Then

```sh
cd .. # back into the workspace repository
git commit -m "pin client artifact $PROJECT$"
```
