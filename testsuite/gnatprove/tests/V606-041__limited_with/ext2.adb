with Ext2_Ext; use Ext2_Ext;
with Unchecked_Deallocation;
package body Ext2 with SPARK_Mode is

   procedure Free is new Unchecked_Deallocation (T1, T1_Acc);

   function Create return T1_Acc is
   begin
      return new T1'(1, 15);
   end Create;

   procedure Update (X : in out T1_Acc) is
      Tmp : Integer := X.F1;
   begin
      X.F1 := X.F2;
      X.F2 := Tmp;
   end Update;

   procedure Dealloc (X : in out T1_Acc) is
   begin
      if X = null then
         return;
      end if;
      Free (X);
   end Dealloc;

end Ext2;
