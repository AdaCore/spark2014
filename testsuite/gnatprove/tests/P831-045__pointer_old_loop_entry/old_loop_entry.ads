pragma SPARK_Mode;
pragma Unevaluated_Use_Of_Old(Allow);
package Old_Loop_Entry is

   type T is access Integer;

   type R is record
      A : T;
   end record;

   type P is access R;

   function Accessor (Ptr : P) return access constant Integer is (Ptr.A);
   function Copy (Ptr : P) return P;

   procedure Proc (X : in out T; Y : in out P) with
     Post => X.all = X.all'Old
       and then Y.A.all = Y.A.all'Old
       and then (declare YY : constant P := Copy(Y)'Old; begin Y.A.all = YY.A.all),
     Contract_Cases =>
       (X = null  => X.all = X.all'Old,
        X /= null => Y.A.all = Y.A.all'Old,
        others    => Y.A.all = Y.A.all'Old
                       and then (declare YY : constant P := Copy(Y)'Old; begin Y.A.all = YY.A.all));

   procedure Bad (X : in out T; Y : in out P) with
     Post => X.all = X'Old.all
       and then Y.A.all = Y.A'Old.all
       and then Y.A.all = Accessor(Y)'Old.all
       and then Y.A.all = Y'Old.A.all,
     Contract_Cases =>
       (X = null  => X.all = X'Old.all,
        X /= null => Y.A.all = Y.A'Old.all
                       and then Y.A.all = Accessor(Y)'Old.all,
        others    => Y.A.all = Y'Old.A.all);

end Old_Loop_Entry;
