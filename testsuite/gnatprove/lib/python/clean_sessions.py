"""Clean up Why3 session XML files by removing unsuccessful proofs."""

import xml.etree.ElementTree as ET

# Prover preference order (lower index = higher preference)
PROVER_PREFERENCE = {"cvc5": 0, "z3": 1, "alt-ergo": 2, "colibri": 3}

# Standard Why3 prover ID mapping (may vary by configuration)
DEFAULT_PROVER_MAP = {
    "0": "cvc5",
    "1": "z3",
    "2": "alt-ergo",
    "3": "colibri",
    "4": "unknown",
}


def get_prover_preference(prover_name):
    """Get preference score for a prover (lower is better)."""
    # Normalize the name (remove whitespace, lowercase)
    normalized = prover_name.strip().lower()

    # Handle common variations
    if normalized in ("cvc5", "cvc4"):
        return PROVER_PREFERENCE["cvc5"]
    elif normalized in ("z3",):
        return PROVER_PREFERENCE["z3"]
    elif normalized in ("alt-ergo", "altergo", "alternative ergo"):
        return PROVER_PREFERENCE["alt-ergo"]
    elif normalized in ("colibri",):
        return PROVER_PREFERENCE["colibri"]

    # Unknown prover gets lowest priority
    return float("inf")


def write_with_doctype_preserved(tree, filepath):
    """
    Write XML tree while preserving the original DOCTYPE declaration.

    ElementTree's write() doesn't preserve DOCTYPE, so we extract it from the
    original file, write the tree, then reconstruct the file with the DOCTYPE.
    """
    # Extract DOCTYPE from the original file
    original_doctype = None
    try:
        with open(filepath, "r", encoding="utf-8") as f:
            for line in f:
                if line.startswith("<!DOCTYPE"):
                    # Collect DOCTYPE lines (might span multiple lines)
                    original_doctype = line
                    while not original_doctype.rstrip().endswith(">"):
                        original_doctype += next(f)
                    break
    except (IOError, StopIteration):
        pass

    # Write the tree using ElementTree
    ET.indent(tree, space="  ")
    tree.write(filepath, encoding="utf-8", xml_declaration=True)

    # If we found a DOCTYPE in the original, reconstruct the file with it
    if original_doctype:
        with open(filepath, "r", encoding="utf-8") as f:
            content = f.read()

        # Split on first newline to separate XML declaration from the rest
        parts = content.split("\n", 1)
        declaration = parts[0] + "\n"
        rest = parts[1] if len(parts) > 1 else ""

        # Reconstruct with DOCTYPE
        new_content = declaration + original_doctype
        if not original_doctype.endswith("\n"):
            new_content += "\n"
        new_content += rest

        # Write back
        with open(filepath, "w", encoding="utf-8") as f:
            f.write(new_content)


def select_best_proof(successful_proofs, prover_map):
    """Select the best proof based on prover preference order."""
    best = None
    best_score = float("inf")

    for proof in successful_proofs:
        prover_id = proof.get("prover")
        prover_name = prover_map.get(prover_id, f"unknown_{prover_id}")
        score = get_prover_preference(prover_name)

        if score < best_score:
            best_score = score
            best = proof

    return best


def extract_prover_map_from_xml(root):
    """Extract prover mapping from the session file's prover elements."""
    prover_map = {}
    for prover in root.findall("prover"):
        prover_id = prover.get("id")
        prover_name = prover.get("name")
        if prover_id and prover_name:
            prover_map[prover_id] = prover_name
    return prover_map


def clean_session_file(filepath, prover_map=None):
    """
    Clean up Why3 session XML file.

    - Removes all unsuccessful proof attempts
    - Keeps only one successful proof per goal
    - Prefers provers in order: cvc5, z3, alt-ergo, colibri
    """
    tree = ET.parse(filepath)
    root = tree.getroot()

    # Extract prover mapping from the session file, warn if falling back to defaults
    if prover_map is None:
        prover_map = extract_prover_map_from_xml(root)
        if not prover_map:
            print(
                f"Warning: {filepath}: no prover elements found in session file,"
                " using default prover numbering"
            )
            prover_map = DEFAULT_PROVER_MAP

    total_goals = 0
    goals_with_removed_proofs = 0
    removed_unsuccessful_proofs = 0
    removed_duplicate_proofs = 0
    goals_with_no_proofs = []

    # Process each goal
    for goal in root.findall(".//goal"):
        total_goals += 1
        proofs = goal.findall("proof")

        if not proofs:
            continue

        proofs_removed_from_goal = 0

        # Separate successful, unsuccessful, and incomplete proofs
        successful_proofs = []
        unsuccessful_proofs = []
        incomplete_proofs = []

        for proof in proofs:
            result = proof.find("result")
            if result is not None:
                if result.get("status") == "valid":
                    # Only count as successful if it has steps information
                    if result.get("steps") is not None:
                        successful_proofs.append(proof)
                    else:
                        incomplete_proofs.append(proof)
                else:
                    unsuccessful_proofs.append(proof)
            else:
                unsuccessful_proofs.append(proof)

        # Remove unsuccessful proofs
        for proof in unsuccessful_proofs:
            goal.remove(proof)
            removed_unsuccessful_proofs += 1
            proofs_removed_from_goal += 1

        # Remove incomplete proofs (valid but missing steps), with a warning
        for proof in incomplete_proofs:
            goal_name = goal.get("name", "unknown")
            prover_id = proof.get("prover", "unknown")
            prover_name = prover_map.get(prover_id, f"unknown_{prover_id}")
            print(
                f"Warning: {filepath}: goal {goal_name!r}:"
                f" removing proof by {prover_name!r} with valid status but no steps"
            )
            goal.remove(proof)
            removed_unsuccessful_proofs += 1
            proofs_removed_from_goal += 1

        # If multiple successful proofs, keep only the best one
        if len(successful_proofs) > 1:
            best_proof = select_best_proof(successful_proofs, prover_map)
            for proof in successful_proofs:
                if proof is not best_proof:
                    goal.remove(proof)
                    removed_duplicate_proofs += 1
                    proofs_removed_from_goal += 1

        if proofs_removed_from_goal > 0:
            goals_with_removed_proofs += 1

        # Check if goal now has no proofs, but originally had valid proofs
        if len(goal.findall("proof")) == 0 and (successful_proofs or incomplete_proofs):
            goal_name = goal.get("name", "unknown")
            goals_with_no_proofs.append(goal_name)

    # Write back to file with proper formatting and DOCTYPE preservation
    write_with_doctype_preserved(tree, filepath)

    return {
        "total_goals": total_goals,
        "goals_with_removed_proofs": goals_with_removed_proofs,
        "removed_unsuccessful_proofs": removed_unsuccessful_proofs,
        "removed_duplicate_proofs": removed_duplicate_proofs,
        "goals_with_no_proofs": goals_with_no_proofs,
    }
