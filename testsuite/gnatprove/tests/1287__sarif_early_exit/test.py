import contextlib
import io
import json
import os.path
import re

from test_support import prove_all, sarif_msg_text

Error_Line = re.compile(r"^.+:\d+:\d+: error: (.+)$")


def extract_cli_messages(output):
    result = []
    for line in output.splitlines():
        match = Error_Line.match(line)
        if match:
            result.append(match.group(1))
    return result


def check_expected_sarif_messages(cli_messages):
    with open(os.path.join("gnatprove", "gnatprove.sarif")) as f:
        sarif = json.load(f)

    actual_messages = {
        sarif_msg_text(result) for result in sarif["runs"][0].get("results", [])
    }

    for msg in cli_messages:
        if msg not in actual_messages:
            print("Missing in SARIF:", msg)


if __name__ == "__main__":
    stream = io.StringIO()
    with contextlib.redirect_stdout(stream):
        prove_all()

    output = stream.getvalue()
    print(output, end="")
    check_expected_sarif_messages(extract_cli_messages(output))
