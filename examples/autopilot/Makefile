.PHONY: codepeer spark

codepeer:
	gnatmake -c -gnatcC -Pautopilot
	codepeer -all -lib test.lib -global
	codepeer_msg_reader test.output || echo ""

spark:
	sparkmake
	-spark -vcg -brief -i=spark.idx -config=autopilot.cfg @spark.smf
	sparksimp -p=4
	pogs
