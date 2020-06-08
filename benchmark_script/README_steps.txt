This README explains a possible route to follow if one wants to assess
rlimit/steps behavior for a prover, or get scaling values for why3.


1) Run create_benchmarks.sh
2) Run collate_benchmarks.py

Refer to README.txt for more information on steps 1 and 2.

3) Run prover_stats.py.

   This script produces a csv file (or JSON, but we use csv here) that contains
   time/steps/result data for a given prover on all VCs for this prover.

   Example:

   python prover_stats.py -j 16 --prover=altergo -t 10 --format csv benchmark_script/bench/altergo/ -o altergo.csv

4) Remove timeout info from the CSV file. Provers either don't output steps for
timeouts, or the steps are not reliable.

   grep -v timeout altergo.csv > altergo-notimeout.csv

5) Analyze the data using R. Run R, then use commands like this:

To read the file into variable "data":

   data <- read.csv("altergo-notimeout.csv")

To plot time depending on steps:

   plot(Time~Steps, data)

To create a linear model:
  
   fit <- lm(Time~Steps, data)
   summary(fit)

To see some statistical data of the linear model:

   a <- anova(fit)
   a


