---
visibility: PRIVATE
---

# TODO: Repo Initialization

- [ ] Rename the directory `QN`, replacing `N` with the current quarter
- [ ] Rename the directory `YYYY`, replacing `YYYY` with the current year
- [ ] Make the following replacements in this file:
  - `$CLIENT$` -> clients name
  - `$client-url` -> client's home page
- [ ] Initialize the report skeleton
  ```sh
  cd YYYY/QN/report
  make init
  ```
- [ ] Add client artifacts to the `artifacts` subdirectory, using the instructions
  in the final section below.
- [ ] Remove this section
- [ ] Invite the client team members to this repo

#  Audit Workspace _of_ Informal Systems ⨯ $CLIENT$

This repository is a workspace for [Informal Systems](https://informal.systems/)
and [$CLIENT$]($client-url$) to collaborate on auditing the software developed
by $CLIENT$.

## Usage and organization

The artifacts for each audit engagement are gathered in a subdirectory named
after the year and quarter in which the audit was carried out.

These artifacts include:

- The artifacts generated the course of the audit.
- The artifacts under audit, referenced as git submodules.

### To clone just the artifacts Informal created during the audit

``` sh
git clone git@github.com:informalsystems/audit-$CLIENT$.git
```

### To clone all artifacts, including Interlay's source code at the relevant commits

``` sh
git clone --recurse-submodules git@github.com:informalsystems/audit-$CLIENT$.git
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

where $TAG$ is the tag or commit agreed to be under audit.

Then

```sh
cd .. # back into the workspace repository
git commit -m "pin client artifact $PROJECT$"
```
