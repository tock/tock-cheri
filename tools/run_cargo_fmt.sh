#!/usr/bin/env bash
#
# Runs rustfmt on all subdirectories with a Cargo.toml file. Must be run from
# root Tock directory. Protects user from inadvertently overwriting files.
#
# Author: Pat Pannuto <pat.pannuto@gmail.com>
# Author: Brad Campbell <bradjc5@gmail.com>
#
set -e

# Verify that we're running in the base directory
if [ ! -x tools/run_cargo_fmt.sh ]; then
	echo ERROR: $0 must be run from the tock repository root.
	echo ""
	exit 1
fi

# Add the rustfmt component if needed.
if ! rustup which rustfmt; then
  if ! rustup component list | grep 'rustfmt.*(installed)' -q; then
    # Some versions of OS X want the -preview version, retry that on failure
    rustup component add rustfmt || rustup component add rustfmt-preview
  fi
fi

# Format overwrites changes, which is probably good, but it's nice to see
# what it has done
#
# `git status --porcelain` formats things for scripting
# | M changed file, unstaged
# |M  changed file, staged (git add has run)
# |MM changed file, some staged and some unstaged changes (git add then changes)
# |?? untracked file
if [ "$1" != "diff" ]; then
	if git status --porcelain | grep '^.M.*\.rs' -q; then
		echo "$(tput bold)Warning: Formatting will overwrite files in place.$(tput sgr0)"
		echo "While this is probably what you want, it's often useful to"
		echo "stage all of your changes (git add ...) before format runs,"
		echo "just so you can double-check everything."
		echo ""
		echo "$(tput bold)git status:$(tput sgr0)"
		git status
		echo ""
		read -p "Continue formatting with unstaged changes? [y/N] " response
		if [[ ! ( "$(echo "$response" | tr :upper: :lower:)" == "y" ) ]]; then
			exit 0
		fi
	fi
fi

set +e
let FAIL=0
set -e

# Get the list of files in the workspace to avoid formatting
# them twice
csplit Cargo.toml '/exclude = \[/' > /dev/null
rm xx01

# Find folders with Cargo.toml files in them and run `cargo fmt`.
for f in $(find . | grep Cargo.toml); do
	if [ $f == './Cargo.toml' ]; then
		printf "\rFormatting Workspace"
		dir='.'
	else
		dir=$(dirname $f)
		dir=${dir:2} # strip leading ./
		if grep -q '"'$dir'"' xx00; then
			continue
		fi

		printf "\rFormatting %-$((39))s" $dir
	fi

	pushd $dir > /dev/null
	if [ "$1" == "diff" ]; then
		# If diff mode, two-pass the check to make pretty-print work
		if ! cargo-fmt -q -- --check; then
			printf "<- Contains formatting errors!\n"
			cargo-fmt -- --check || let FAIL=FAIL+1
			printf "\n"
		fi
	else
		cargo-fmt
	fi
	popd > /dev/null
done
rm xx00
printf "\rFormatting complete. %-$((39))s\n" ""

# Check for tab characters in Rust source files that haven't been
# removed by rustfmt
RUST_FILES_WITH_TABS="$(git grep --files-with-matches $'\t' -- '*.rs' || grep -lr --include '*.rs' $'\t' . || true)"
if [ "$RUST_FILES_WITH_TABS" != "" ]; then
        echo "ERROR: The following files contain tab characters, please use spaces instead:"
        echo "$RUST_FILES_WITH_TABS" | sed 's/^/    -> /'
        let FAIL=FAIL+1
fi

if [[ $FAIL -ne 0 ]]; then
	echo
	echo "$(tput bold)Formatting errors.$(tput sgr0)"
	echo "See above for details"
fi
exit $FAIL
