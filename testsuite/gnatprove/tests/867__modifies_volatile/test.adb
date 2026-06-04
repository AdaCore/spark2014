with Ext;
procedure Test with SPARK_Mode is

   --  Effectively volatile data that is an output of the subprogram should be
   --  mentioned in the Modifies aspect.

   Y : Integer;

   procedure P_Volatile_Bad_1 with
     Modifies => Y
   is
   begin
      Y := Ext.X.G;
      Ext.X.F := 15;
   end P_Volatile_Bad_1;

   procedure P_Volatile_Bad_2 with
     Modifies => (Y, Ext.X.F)
   is
   begin
      Y := Ext.X.G;
      Ext.X.F := 15;
   end P_Volatile_Bad_2;

   procedure P_Volatile_Bad_3 (B : Boolean) with
     Modifies => (Y, Ext.X when B)
   is
   begin
      Y := Ext.X.G;
      if B then
         Ext.X.F := 15;
      end if;
   end P_Volatile_Bad_3;

   procedure P_Volatile_Ok with
     Modifies => (Y, Ext.X)
   is
   begin
      Y := Ext.X.G;
      Ext.X.F := 15;
   end P_Volatile_Ok;

   procedure P_Protected_Bad with
     Modifies => Y
   is
   begin
      Y := Ext.X.G;
      Ext.Prot.P;
   end P_Protected_Bad;

   procedure P_Protected_Bad_2 (B : Boolean) with
     Modifies => (Y, Ext.Prot when B)
   is
   begin
      Y := Ext.X.G;
      if B then
         Ext.Prot.P;
      end if;
   end P_Protected_Bad_2;

   procedure P_Protected_Ok with
     Modifies => (Y, Ext.Prot)
   is
   begin
      Y := Ext.X.G;
      Ext.Prot.P;
   end P_Protected_Ok;
begin
   null;
end;
