#!/bin/bash

ORIGINALS_DIR="../../Problems/Originals"
BASE_TARGET_DIR="../../parsed_problems"

PGEON_DIR="$BASE_TARGET_DIR/pgeon"
PGEON_UNK_DIR="$PGEON_DIR/UNK"

TWB_DIR="$BASE_TARGET_DIR/twb"
TWB_UNK_DIR="$TWB_DIR/UNK"

mkdir -p "$PGEON_DIR" "$PGEON_UNK_DIR"
mkdir -p "$TWB_DIR" "$TWB_UNK_DIR"

echo "Beginning translation of TPTP problems..."
echo "----------------------------------------"

for filepath in "$ORIGINALS_DIR"/*.p; do
    [ -e "$filepath" ] || continue

    filename=$(basename "$filepath")
    filename_no_ext="${filename%.*}"

    echo "Parsing $filename ..."

    dune exec parser -- --pgeon "$filepath" > "$PGEON_DIR/$filename" 2>/dev/null
    exit_status=$?

    if [ $exit_status -ne 0 ]; then
        echo "  [Pgeon] Error while parsing $filename"
        rm -f "$PGEON_DIR/$filename"
    else
        if [ -f "UNK_pos_$filename" ] || [ -f "UNK_neg_$filename" ]; then
            [ -f "UNK_pos_$filename" ] && mv "UNK_pos_$filename" "$PGEON_UNK_DIR/"
            [ -f "UNK_neg_$filename" ] && mv "UNK_neg_$filename" "$PGEON_UNK_DIR/"
            rm -f "$PGEON_DIR/$filename"
            echo "   -> [Pgeon] Generated split files in pgeon/UNK/ (.p)"
        fi
    fi

    dune exec parser -- --twb "$filepath" > "$TWB_DIR/$filename_no_ext.twb" 2>/dev/null
    exit_status=$?

    if [ $exit_status -ne 0 ]; then
        echo "  [TWB] Error while parsing $filename"
        rm -f "$TWB_DIR/$filename_no_ext.twb"
    else
        if [ -f "UNK_pos_$filename" ] || [ -f "UNK_neg_$filename" ]; then
            [ -f "UNK_pos_$filename" ] && mv "UNK_pos_$filename" "$TWB_UNK_DIR/UNK_pos_$filename_no_ext.twb"
            [ -f "UNK_neg_$filename" ] && mv "UNK_neg_$filename" "$TWB_UNK_DIR/UNK_neg_$filename_no_ext.twb"
            rm -f "$TWB_DIR/$filename_no_ext.twb"
            echo "   -> [TWB] Generated split files in twb/UNK/ (.twb)"
        fi
    fi

done

echo "----------------------------------------"
echo "Finished ! All translated files were organized in:"
echo "  -> Pgeon: $PGEON_DIR"
echo "  -> TWB  : $TWB_DIR"