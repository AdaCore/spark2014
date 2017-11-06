package body Cannot_Inline with
  SPARK_Mode
is

   function Return_String return String;
   procedure Has_Local_Subprogram;
   procedure Has_Local_Subprogram_In_Block;

   function Return_String return String is
   begin
      return "bla";
   end Return_String;

   procedure Has_Local_Subprogram is
      procedure Local is
      begin
         null;
      end Local;
   begin
      Local;
   end Has_Local_Subprogram;

   procedure Has_Local_Subprogram_In_Block is
   begin
      declare
         procedure Local is
         begin
            null;
         end Local;
      begin
         Local;
      end;
   end Has_Local_Subprogram_In_Block;

   package Has_Pending_Instantiations is
      generic
         V : Integer;
      package P is
         function Get return Integer;
      end P;

      procedure Proc;
   end Has_Pending_Instantiations;

   package body Has_Pending_Instantiations is
      package body P is
         function Get return Integer is
         begin
            return V;
         end Get;
      end P;

      procedure Other is
         package One is new P (1);
      begin
         null;
      end Other;

      procedure Proc is
      begin
         null;
      end Proc;
   end Has_Pending_Instantiations;

   procedure Test is
      S : String := Return_String;
   begin
      Has_Local_Subprogram;
      Has_Local_Subprogram_In_Block;
      Has_Pending_Instantiations.Proc;
   end Test;

end Cannot_Inline;
