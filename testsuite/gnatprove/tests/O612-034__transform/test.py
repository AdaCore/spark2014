from test_support import prove_all, sleep, touch
import os.path
import xml.etree.ElementTree as ET

# This test checks that gnatprove preserves a transformation inserted manually
# into the current Why3 session when the proof machinery is rerun.

session_file = os.path.join("gnatprove", "test__p", "why3session.xml")


def parse_session():
    return ET.parse(session_file)


def find_target_goal(root):
    for goal in root.iter("goal"):
        if any(child.tag == "proof" for child in goal):
            return goal
    raise RuntimeError("could not find a goal with direct proof attempts")


def count_inline_goal(goal):
    return sum(
        1
        for child in goal
        if child.tag == "transf" and child.get("name") == "inline_goal"
    )


def inject_manual_transform():
    tree = parse_session()
    goal = find_target_goal(tree.getroot())
    if count_inline_goal(goal) != 0:
        raise RuntimeError("unexpected pre-existing inline_goal transformation")

    inline = ET.Element("transf", {"name": "inline_goal", "expanded": "true"})
    ET.SubElement(
        inline,
        "goal",
        {
            "name": goal.get("name", "manual_goal") + ".manual",
            "expl": goal.get("expl", ""),
        },
    )
    goal.append(inline)
    tree.write(session_file, encoding="utf-8", xml_declaration=True)


def print_inline_goal_count():
    goal = find_target_goal(parse_session().getroot())
    print(count_inline_goal(goal))


# run gnatprove once
prove_all(cache_allowed=False)
# print the number of manually inserted inline_goal transformations
print_inline_goal_count()
# inject one transformation into the freshly generated session
inject_manual_transform()
sleep(4)
# touch file after a delay so the next gnatprove run replays the updated
# session against a strictly newer source timestamp
touch("test.adb")
# run gnatprove again and check that the inserted transformation survived
prove_all(cache_allowed=False)
print_inline_goal_count()
