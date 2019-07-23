pragma SPARK_Mode;
pragma Unevaluated_Use_Of_Old(Allow);
procedure Lib_Level (X : in out T; Y : in out P) is
begin
  for I in 1 .. 10 loop
     pragma Loop_Invariant (X.all = X'Loop_Entry.all);
     pragma Loop_Invariant (Y.A.all = Y.A'Loop_Entry.all);
     pragma Loop_Invariant (Y.A.all = Accessor(Y)'Loop_Entry.all);
     pragma Loop_Invariant (Y.A.all = Y'Loop_Entry.A.all);
     pragma Loop_Variant (Increases => X.all - X'Loop_Entry.all);
     pragma Loop_Variant (Decreases => Y.A.all - Y.A'Loop_Entry.all);
     pragma Loop_Variant
       (Increases => Y.A.all - Accessor(Y)'Loop_Entry.all,
        Decreases => Y.A.all - Y'Loop_Entry.A.all);
  end loop;
end Lib_Level;

