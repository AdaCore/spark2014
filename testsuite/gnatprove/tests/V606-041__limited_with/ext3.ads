limited with Ext2_Ext;
package Ext3 with SPARK_Mode is

   type T1_Acc is private with
     Default_Initial_Condition => Is_Null (T1_Acc);

   function Is_Null (X : T1_Acc) return Boolean;

   function Create return T1_Acc with
     Post => not Is_Null (Create'Result);

   procedure Update (X : in out T1_Acc) with
     Pre => not Is_Null (X);

   procedure Dealloc (X : in out T1_Acc) with
     Post => Is_Null (X);

private
   type T1_Acc is access Ext2_Ext.T1;

   function Is_Null (X : T1_Acc) return Boolean is (X = null);

   pragma Assert (not Is_Null (Create));

end Ext3;
