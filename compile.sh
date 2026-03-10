#!/usr/bin/bash

disable_sans_math="0"
if [ "$1" == "--disable-sans-math" ]; then
    disable_sans_math="1"
fi

# Turns path of document into a displayable name (just swaps / for - and removes the extension)
# Collect documents:
#  .typ files that don't contain FLASHBANG IGNORE (explicit) or FLASHBANG INCLUDE (library files not meant to contain cards)
documents=()
while IFS=  read -r -d $'\0'; do
    if ! grep -F -q -e '//![FLASHBANG IGNORE]' -e '//![FLASHBANG INCLUDE]' "$REPLY"; then
        documents+=("$REPLY")
    fi
done < <(find . -name "*.typ" -not -path "./dist/*" -printf "%P\0")
# ^ think of excluding dist

mkdir -p ./cache/src

src="./cache/src/_full.typ"
full="./public/static/_full.pdf"

# Merged file header
echo -e "#import \"../../cards.typ\": *\n#show: setup" > "$src"

# Build merged source
for doc in "${documents[@]}"; do

    # start new section (avoids polluting global scope)
    echo "#[" >> "$src"
    awk '/^\/\/!\[FLASHBANG HEADER\]/{flag=1;next} flag' "$doc" >> "$src"
    echo "]" >> "$src"
done

# Make local cache home
mkdir -p ./cache
CACHE="$(realpath ./cache)"

# Compile merged file
>&2 echo "compiling $src -> $full"
XDG_CACHE_HOME="$CACHE" typst compile --root . --font-path "./fonts/" --ignore-system-fonts --input "disable_sans_math=$disable_sans_math" "$src" "$full"
