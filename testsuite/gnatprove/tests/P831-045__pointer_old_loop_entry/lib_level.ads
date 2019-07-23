pragma SPARK_Mode;
pragma Unevaluated_Use_Of_Old(Allow);
with Old_Loop_Entry; use Old_Loop_Entry;
procedure Lib_Level (X : in out T; Y : in out P) with
     Post => X.all = X'Old.all
       and then Y.A.all = Y.A'Old.all
       and then Y.A.all = Accessor(Y)'Old.all
       and then Y.A.all = Y'Old.A.all,
     Contract_Cases =>
       (X = null  => X.all = X'Old.all,
        X /= null => Y.A.all = Y.A'Old.all
                       and then Y.A.all = Accessor(Y)'Old.all,
        others    => Y.A.all = Y'Old.A.all);

