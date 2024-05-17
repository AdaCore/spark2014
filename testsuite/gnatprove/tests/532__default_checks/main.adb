with Ext;
procedure Main with SPARK_Mode is

   --  This test checks that we are not missing default checks with record abstraction.

   X1 : Ext.P1.R;
   X2 : Ext.P2.R;
   X3 : Ext.P3.R;
   X4 : Ext.P4.R;
   X5 : Ext.P5.R;
   X6 : Ext.P6.R;
   X7 : Ext.P7.R;
   X8 : Ext.P8.R;
   X9 : Ext.P9.R; --  @PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
   X10 : Ext.P10.R; --  @PREDICATE_CHECK_ON_DEFAULT_VALUE:FAIL
   X11 : Ext.P11.R;
   X12 : Ext.P12.R;
   X13 : Ext.P13.R;
   X14 : Ext.P14.R;

begin
   null;
end Main;
