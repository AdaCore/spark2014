import re

from test_support import capture_prove_all, sarif_results, sarif_msg_text

Error_Line = re.compile(r"^.+:\d+:\d+: error: (.+)$")


def extract_cli_messages(output):
    result = []
    for line in output.splitlines():
        match = Error_Line.match(line)
        if match:
            result.append(match.group(1))
    return result


def check_expected_sarif_messages(cli_messages):
    actual_messages = {sarif_msg_text(result) for result in sarif_results()}

    for msg in cli_messages:
        if msg not in actual_messages:
            print("Missing in SARIF:", msg)


if __name__ == "__main__":
    output = capture_prove_all()
    print(output, end="")
    check_expected_sarif_messages(extract_cli_messages(output))
