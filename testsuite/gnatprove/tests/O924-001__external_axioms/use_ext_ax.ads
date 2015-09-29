with Ext_Ax; use Ext_Ax;
with G_Ext_Ax;
package Use_Ext_Ax with SPARK_Mode is
   subtype TT1 is T1;
   subtype TT2 is T2;
   subtype PT1 is P.T1;
   subtype PT2 is P.T2;

   package Nested_Ext_Ax with SPARK_Mode => Off is
      pragma Annotate (GNATprove, External_Axiomatization);
      type T1 is private;
      type T2 is new Integer;

      package P is new G_Ext_Ax;

   private
      type T1 is new Integer;
   end Nested_Ext_Ax;
end Use_Ext_Ax;
