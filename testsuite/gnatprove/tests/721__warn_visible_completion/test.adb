with Ext_1; use Ext_1;

procedure Test with SPARK_Mode is

   package Inner is
      type T is private;
   private
      type C;
      type T is access C;
   end Inner;

   package body Inner is
      type C is new Integer;
   end Inner;

   package Inst is new Gen;

begin
   null;
end Test;
