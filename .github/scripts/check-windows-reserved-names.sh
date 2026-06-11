#!/usr/bin/env bash
set -euo pipefail
export LC_ALL=C

reserved_pattern='^(con|prn|aux|nul|clock\$|com[1-9]|lpt[1-9])$'
found_reserved=0

check_component() {
  local path="$1"
  local component="$2"

  [[ -z "$component" ]] && return 0

  local lower="${component,,}"
  local stem="${lower%%.*}"

  if [[ "$stem" =~ $reserved_pattern ]]; then
    echo "::error file=${path}::reserved Windows device-name path component '${component}' in '${path}'"
    found_reserved=1
  fi
}

while IFS= read -r -d '' path; do
  remaining="$path"

  while :; do
    component="${remaining%%/*}"
    check_component "$path" "$component"

    [[ "$remaining" == */* ]] || break
    remaining="${remaining#*/}"
  done
done < <(git ls-files -z --cached --others --exclude-standard)

if (( found_reserved != 0 )); then
  exit 1
fi
