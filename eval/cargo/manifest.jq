def line:
  "  " + (.name)
  + " = { version = \"" + (.req) + "\""
  + (if .optional then ", optional = true" else "" end)
  # NOT `// true`: jq's // treats explicit false as missing
  + (if .default_features == false then ", default-features = false" else "" end)
  + (if ((.features // []) | length) > 0
     then ", features = [" + ((.features | map("\"" + . + "\"")) | join(", ")) + "]"
     else "" end)
  + (if .package then ", package = \"" + .package + "\"" else "" end)
  + " }";

# features2 carries the v2-schema dep:/dep?/ entries the index moved out
# of features for old-cargo compatibility; a key in both contributes to
# one feature (concatenated), matching cargo_parse.ml's feature_table.
def mergedFeatures:
  (.features // {}) as $f
  | (.features2 // {}) as $f2
  | (($f | keys) + ($f2 | keys) | unique) as $ks
  | reduce $ks[] as $k ({}; .[$k] = (($f[$k] // []) + ($f2[$k] // [])));

def header($target; $kind):
  (if $kind == "normal" then "dependencies"
   elif $kind == "dev" then "dev-dependencies"
   else "build-dependencies" end) as $k
  | if $target == "" then "[" + $k + "]"
    else "[target.'" + $target + "'." + $k + "]" end;

def sections:
  [ .deps[] | { target: (.target // ""), kind: (.kind // "normal"), body: line } ]
  | group_by([.target, .kind])
  | map(header(.[0].target; .[0].kind) + "\n" + ((. | map(.body)) | join("\n")))
  | join("\n\n");

(if .rust_version then "rust-version = \"" + .rust_version + "\"\n" else "" end) as $rv
# cargo refuses a links key without a build script; build_manifest writes one
| (if .links then "links = \"" + .links + "\"\nbuild = \"build.rs\"\n" else "" end) as $links
| "[package]\nname = \"" + .name + "\"\nversion = \"" + .vers
# the index carries no edition, and 2015 imposes no rustc floor of its
# own, so the declared rust-version stays the only rustc constraint
+ "\"\nedition = \"2015\"\nresolver = \"3\"\n" + $rv + $links + "\n"
+ "[lib]\npath = \"src/lib.rs\"\n\n[features]\n"
+ (mergedFeatures | to_entries
   | map(.key + " = [" + ((.value | map("\"" + . + "\"")) | join(", ")) + "]")
   | join("\n"))
+ "\n\n" + sections + "\n"
