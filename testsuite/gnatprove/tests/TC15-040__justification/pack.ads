package Pack
  with Initializes => null
is
   Var : Integer := 0;
   pragma Annotate (GNATprove, Intentional,
                    "initialization of ""Var"" must be mentioned in the Initializes contract of ""Pack"" (SPARK RM 7.1.5(9))",
                    "test for pragma Annotate");
end Pack;
