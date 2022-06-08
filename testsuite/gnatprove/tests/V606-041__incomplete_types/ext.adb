with Unchecked_Deallocation;
package body Ext with SPARK_Mode is

   type Int_Acc is access Integer;
   procedure Free is new Unchecked_Deallocation (Integer, Int_Acc);

   type T1 is record
      F1 : Integer;
      F2 : not null Int_Acc;
   end record;

   procedure Free is new Unchecked_Deallocation (T1, T1_Acc);

   function Create return T1_Acc is
   begin
      return new T1'(1, new Integer'(15));
   end Create;

   procedure Update (X : in out T1_Acc) is
      Tmp : Integer := X.F1;
   begin
      X.F1 := X.F2.all;
      X.F2.all := Tmp;
   end Update;

   procedure Dealloc (X : in out T1_Acc) is
      Tmp : Int_Acc;
   begin
      if X = null then
         return;
      end if;
      Tmp := X.F2;
      Free (Tmp);
      Free (X);
   end Dealloc;

end Ext;
