import re

from test_support import OutputRefiner, default_refiners_no_sort, prove_all


class StatisticsTimingRefiner(OutputRefiner):
    def refine(self, lines: list[str]) -> list[str]:
        return [
            re.sub(r"in max [0-9.]+ seconds", "in max <TIME> seconds", line)
            for line in lines
        ]


prove_all(
    report="statistics",
    refiners=default_refiners_no_sort() + [StatisticsTimingRefiner()],
)
