The script here can be used to analyse step usage for CVC4.

make_stats.py

   This reads from directory cvc4 and produces either stats for the
   spectral analysis (how steps are consumed, on average over time) or
   provability analysis the examine how an increase in "steps" affects the
   results.

Use process_spectrum.py or process.py respectively.

You'll need to change these scripts as they don't support command-line
flags.
