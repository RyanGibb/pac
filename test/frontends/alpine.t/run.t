  $ ../../../src/main.exe alpine APKINDEX app docs | sed -E '/^(parse|solve) [0-9.]+s$/d'
  index APKINDEX
  cone: 3 packages, 0 provide rows, 1 install_if rows
  packages (3):
    app 1.0
    app-doc 1.0
    docs 1.0
  encoded solution: 8 core nodes (4 Alpine packages encoded)
