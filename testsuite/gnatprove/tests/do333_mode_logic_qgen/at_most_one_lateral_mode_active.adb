--  Copyright (C) Your Company Name
--
--  @generated with QGen Code Generator 2.0.0w (20150420)
--  Command line arguments:
--    --clean models/case_studies/NASA-DO-333-Case-Studies/Mode_Logic_Case_Study_Files/Mode_Logic_Props.mdl
--    --output models/case_studies/NASA-DO-333-Case-Studies/Mode_Logic_Case_Study_Files/Mode_Logic_Props/hmc_ada
--    --language ada
--    --debug
--    --typing models/case_studies/NASA-DO-333-Case-Studies/Mode_Logic_Case_Study_Files/Mode_Logic_Props_types.txt

pragma Style_Checks ("M999");  --  ignore long lines

package body At_Most_One_Lateral_Mode_Active is

   procedure comp
      (ROLL_Active : Boolean;
       HDG_Active : Boolean;
       NAV_Active : Boolean;
       LAPPR_Active : Boolean;
       LGA_Active : Boolean)
   is
      use type Boolean;
      HDG_Active_out1 : Boolean;
      LAPPR_Active_out1 : Boolean;
      LGA_Active_out1 : Boolean;
      NAV_Active_out1 : Boolean;
      ROLL_Active_out1 : Boolean;
      NOR_LGA_out1 : Boolean;
      NOT1_out1 : Boolean;
      NOT5_out1 : Boolean;
      NOR_LAPPR_out1 : Boolean;
      NOT1_out1_1 : Boolean;
      NOT5_out1_1 : Boolean;
      NOR_NAV_out1 : Boolean;
      NOT1_out1_2 : Boolean;
      NOT5_out1_2 : Boolean;
      NOR_HDG_out1 : Boolean;
      NOT1_out1_3 : Boolean;
      NOT5_out1_3 : Boolean;
      NOR_ROLL_out1 : Boolean;
      NOT1_out1_4 : Boolean;
      NOT5_out1_4 : Boolean;
      AND_out1 : Boolean;
   begin
      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/HDG_Active
      HDG_Active_out1 := HDG_Active;
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/HDG_Active

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/LAPPR_Active
      LAPPR_Active_out1 := LAPPR_Active;
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/LAPPR_Active

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/LGA_Active
      LGA_Active_out1 := LGA_Active;
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/LGA_Active

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NAV_Active
      NAV_Active_out1 := NAV_Active;
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NAV_Active

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/ROLL_Active
      ROLL_Active_out1 := ROLL_Active;
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/ROLL_Active

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NOR_LGA
      NOR_LGA_out1 := not  ((((ROLL_Active_out1)
         or else (HDG_Active_out1))
            or else (NAV_Active_out1))
               or else (LAPPR_Active_out1));
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NOR_LGA

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies4/NOT1
      NOT1_out1 := not  (LGA_Active_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies4/NOT1

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies4/NOT5
      NOT5_out1 := (NOT1_out1)
         or else (NOR_LGA_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies4/NOT5

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NOR_LAPPR
      NOR_LAPPR_out1 := not  ((((ROLL_Active_out1)
         or else (HDG_Active_out1))
            or else (NAV_Active_out1))
               or else (LGA_Active_out1));
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NOR_LAPPR

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies3/NOT1
      NOT1_out1_1 := not  (LAPPR_Active_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies3/NOT1

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies3/NOT5
      NOT5_out1_1 := (NOT1_out1_1)
         or else (NOR_LAPPR_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies3/NOT5

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NOR_NAV
      NOR_NAV_out1 := not  ((((ROLL_Active_out1)
         or else (HDG_Active_out1))
            or else (LAPPR_Active_out1))
               or else (LGA_Active_out1));
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NOR_NAV

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies2/NOT1
      NOT1_out1_2 := not  (NAV_Active_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies2/NOT1

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies2/NOT5
      NOT5_out1_2 := (NOT1_out1_2)
         or else (NOR_NAV_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies2/NOT5

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NOR_HDG
      NOR_HDG_out1 := not  ((((ROLL_Active_out1)
         or else (NAV_Active_out1))
            or else (LAPPR_Active_out1))
               or else (LGA_Active_out1));
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NOR_HDG

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies1/NOT1
      NOT1_out1_3 := not  (HDG_Active_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies1/NOT1

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies1/NOT5
      NOT5_out1_3 := (NOT1_out1_3)
         or else (NOR_HDG_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies1/NOT5

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NOR_ROLL
      NOR_ROLL_out1 := not  ((((HDG_Active_out1)
         or else (NAV_Active_out1))
            or else (LAPPR_Active_out1))
               or else (LGA_Active_out1));
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/NOR_ROLL

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies/NOT1
      NOT1_out1_4 := not  (ROLL_Active_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies/NOT1

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies/NOT5
      NOT5_out1_4 := (NOT1_out1_4)
         or else (NOR_ROLL_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Implies/NOT5

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/AND
      AND_out1 := ((((NOT5_out1_4)
         and then (NOT5_out1_3))
            and then (NOT5_out1_2))
               and then (NOT5_out1_1))
                  and then (NOT5_out1);
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/AND

      --  Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Assertion
      pragma Assert (AND_out1, "Violation of assertion at block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Assertion");
      --  End Block Mode_Logic_Props/Requirements/At_Most_One_Lateral_Mode_Active/My_Assertion
   end comp;
end At_Most_One_Lateral_Mode_Active;
--  @EOF
