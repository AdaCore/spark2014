package File_System
  with SPARK_Mode
is
   type File is tagged private;

   procedure Create (F : out File) with
     Post'Class => F.Closed,
     Global     => null,
     Annotate   => (GNATprove, Always_Return);

   procedure Open_Read (F : in out File) with
     Pre'Class  => F.Closed,
     Post'Class => F.Is_Open,
     Global     => null,
     Annotate   => (GNATprove, Always_Return);

   procedure Open_Read_Write (F : in out File) with
     Pre'Class  => F.Closed,
     Post'Class => F.Is_Open and F.Is_Writable,
     Global     => null,
     Annotate   => (GNATprove, Always_Return);

   procedure Close (F : in out File) with
     Pre'Class  => F.Is_Open,
     Post'Class => F.Closed,
     Global     => null,
     Annotate   => (GNATprove, Always_Return);

   function Closed (F : File) return Boolean with
     Global   => null;
   function Is_Open (F : File) return Boolean with
     Global   => null;
   function Is_Writable (F : File) return Boolean with
     Global   => null;

private
   type State is (Closed, Open_Read, Open_Read_Write);

   type File is tagged record
      Filename : String (1 .. 20);
      Cursor   : Integer;
      Status   : State;
   end record;

end File_System;
