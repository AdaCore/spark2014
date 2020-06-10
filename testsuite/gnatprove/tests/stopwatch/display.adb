with TuningData;
with System.Storage_Elements;

package body Display with
  SPARK_Mode,
  Refined_State => (LCD => Control)
is

   protected Control is
      pragma Priority (TuningData.DisplayPriority);
      procedure Set_Zero;
      procedure Add_One;
   private
      Current : Natural := 0;
   end Control;

   --  External variable Port is a virtual protected object. All accesses to
   --  Port are mediated by protected object Internal_State, which is
   --  specified with the Part_Of aspect on Port.
   Port : Integer := 0 with
     Volatile,
     Async_Readers,
     Address => System.Storage_Elements.To_Address (16#FFFF_FFFF#),
     Part_Of => Control;

   protected body Control is
      procedure Set_Zero is
      begin
         Current := 0;
         Port    := Current;
      end Set_Zero;

      procedure Add_One is
      begin
         if Current < Natural'Last then
            --  We just stop time at this point.
            Current := Current + 1;
         end if;
         Port := Current;
      end Add_One;
   end Control;

   procedure Initialize with
     Refined_Global  => (Output => Control),
     Refined_Depends => (Control => null)
   is
   begin
      Control.Set_Zero;
      pragma Annotate (GNATprove, False_Positive,
                       "constituent of ""LCD"" is not set",
                       "Set_Zero really does initialize.");
   end Initialize;

   procedure AddSecond with
     Refined_Global  => (In_Out => Control),
     Refined_Depends => (Control => Control)
   is
   begin
      Control.Add_One;
   end AddSecond;

end Display;
