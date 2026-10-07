# Negative test: corrupt one printed number of Table tab:cert (row (94,25): t 12 -> 13); paperCert_ok must FAIL.
# usage (from the project root): bash tools/neg_test.sh
sed 's/⟨94, 25, Test.L3 21 0, 1, 21, 21, 12⟩/⟨94, 25, Test.L3 21 0, 1, 21, 21, 13⟩/' Srg154/PaperTables.lean > /tmp/neg_test.lean
sed -i 's/^namespace Srg154$/namespace Srg154Neg\nopen Srg154/; s/^end Srg154$/end Srg154Neg/' /tmp/neg_test.lean
if lake env lean /tmp/neg_test.lean 2>&1 | grep -q "error"; then echo "NEGATIVE TEST OK (corrupted table rejected)"; else echo "NEGATIVE TEST FAILED"; fi
