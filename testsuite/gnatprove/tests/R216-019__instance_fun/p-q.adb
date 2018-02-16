with P.UID;

package body P.Q
with Refined_State => (Hash => (UIDs.Pool)),
     SPARK_MODE    => Off
is

   package UIDs is new P.UID (Integer);
   use UIDs;

   procedure Foo (ID : out Integer)
   with Refined_Global => (In_Out => UIDs.Pool),
        Refined_Post => (Is_Allocated (ID))
   is
   begin
      null;
   end Foo;

end P.Q;
