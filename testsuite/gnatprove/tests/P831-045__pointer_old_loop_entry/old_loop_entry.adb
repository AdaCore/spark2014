pragma SPARK_Mode;
pragma Unevaluated_Use_Of_Old(Allow);
package body Old_Loop_Entry is

   function Copy (Ptr : P) return P is
      Res : P := new R;
   begin
      Res.A := new Integer'(Ptr.A.all);
      return Res;
   end Copy;

   procedure Proc (X : in out T; Y : in out P) is
   begin
      loop
         pragma Loop_Invariant (X.all = X.all'Loop_Entry);
         pragma Loop_Invariant (Y.A.all = Y.A.all'Loop_Entry);
         pragma Loop_Invariant (Y.A.all = Copy(Y)'Loop_Entry.A.all);
         pragma Loop_Variant (Increases => X.all - X.all'Loop_Entry);
         pragma Loop_Variant (Decreases => Y.A.all - Y.A.all'Loop_Entry);
         pragma Loop_Variant (Increases => Y.A.all - Copy(Y)'Loop_Entry.A.all);
      end loop;
   end Proc;

   procedure Bad (X : in out T; Y : in out P) is
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
   end Bad;

   procedure Bad_Body (X : in out T; Y : in out P) with
     Post => X.all = X'Old.all
       and then Y.A.all = Y.A'Old.all
       and then Y.A.all = Accessor(Y)'Old.all
       and then Y.A.all = Y'Old.A.all,
     Contract_Cases =>
       (X = null  => X.all = X'Old.all,
        X /= null => Y.A.all = Y.A'Old.all
                       and then Y.A.all = Accessor(Y)'Old.all,
        others    => Y.A.all = Y'Old.A.all)
   is
   begin
      null;
   end Bad_Body;

end Old_Loop_Entry;

