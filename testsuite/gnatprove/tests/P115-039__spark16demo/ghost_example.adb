package body Ghost_Example is

   procedure Init (Done : out Boolean) is
      Successful : Boolean := True;
   begin
      --  initialization work
      if Successful then
         Done := True;
         State := Init_Done;
      else
         Done := False;
      end if;
   end Init;

   procedure First_Work_Item (Done : out Boolean) is
      Successful : Boolean := False;
   begin
      --  first part of work
      if Successful then
         Done := True;
         State := In_Progress;
      else
         Done := False;
      end if;
   end First_Work_Item;

   procedure Second_Work_Item (Done : out Boolean) is
      Successful : Boolean := False;
   begin
      --  second part of work
      if Successful then
         Done := True;
         State := All_Done;
      else
         Done := False;
      end if;
   end Second_Work_Item;

   procedure Reset is
   begin
      --  reset application data
      State := Start;
   end Reset;

end Ghost_Example;
