with Step_Function; use Step_Function;
with GNAT.IO; use GNAT.IO;

procedure Step_Function_Test is pragma SPARK_Mode (On);
   SFun1 : Step_Function_t :=
     (Number_Of_Delimiters => 2,
      Step => ((Delimiter => 0, Value => 3.0),
               (Delimiter => 3, Value => 2.0),
               (Delimiter => 5, Value => 5.0),
               others => (Delimiter => 0, Value => 0.0)));

   SFun2 : Step_Function_t :=
     (Number_Of_Delimiters => 2,
      Step => ((Delimiter => 0, Value => 1.0),
               (Delimiter => 3, Value => 1.0),
               (Delimiter => 5, Value => 3.0),
               others => (Delimiter => 0, Value => 0.0)));

   sfun3 : Step_Function_t :=
     (Number_Of_Delimiters => 5,
      Step => ((Delimiter => 0, Value => 1.0),
               (Delimiter => 1, Value => 1.0),
               (Delimiter => 3, Value => 3.0),
               (Delimiter => 5, Value => 5.0),
               (Delimiter => 7, Value => 7.0),
               (Delimiter => 9, Value => 9.0),
               others => (Delimiter => 0, Value => 0.0)));

   sfun4 : Step_Function_t :=
     (Number_Of_Delimiters => 5,
      Step => ((Delimiter => 0, Value => 10.0),
               (Delimiter => 2, Value => 8.0),
               (Delimiter => 4, Value => 6.0),
               (Delimiter => 6, Value => 4.0),
               (Delimiter => 8, Value => 2.0),
               (Delimiter => 10, Value => 0.5),
               others => (Delimiter => 0, Value => 0.0)));

   sfun_merge : Step_Function_t;
begin
   Pragma Assert (Is_Valid(SFun1));
   Pragma Assert (Is_Valid(SFun2));
   Pragma Assert (Step_Function.Is_Valid(sfun3));
   Pragma Assert (Step_Function.Is_Valid(sfun4));

   Pragma Assert (Get_Value(SFun1, 0) = 3.0);
   Pragma Assert (Get_Value(SFun1, 1) = 3.0);
   Pragma Assert (Get_Value(SFun1, 3) = 2.0);
   Pragma Assert (Get_Value(SFun1, 4) = 2.0);
   Pragma Assert (Get_Value(SFun1, 5) = 5.0);
   Pragma Assert (Get_Value(SFun1,
     Function_Range'Last) = 5.0);

   Pragma Assert (Has_Same_Delimiters(SFun1, SFun2));

   Restrictive_Merge(sfun3, sfun4, sfun_merge);

   for i in Function_Range'First..12 loop
--        Put (Float'Image(Get_Value(sfun_merge, i)));
--        New_line;
      Pragma Assert (Get_Value(sfun_merge, i)
                     = Min(Get_Value(sfun3, i), Get_Value(sfun4, i)));
   end loop;

   Pragma Assert (Minimum_Until_Point(sfun4, 1) = 10.0);
   Pragma Assert (Minimum_Until_Point(sfun4, 5) = 6.0);
   Pragma Assert (Minimum_Until_Point(sfun_merge, 11) = 0.5);
end;
