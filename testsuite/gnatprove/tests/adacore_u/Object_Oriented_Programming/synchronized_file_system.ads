with File_System;

package Synchronized_File_System
  with SPARK_Mode
is
   type S_File is new File_System.File with private;

   procedure Create (F : out S_File) with
     Post'Class => F.Closed,
     Global     => null,
     Always_Terminates;

   procedure Open_Read (F : in out S_File) with
     Pre'Class  => F.Closed,
     Post'Class => F.Is_Open,
     Global     => null,
     Always_Terminates;

   procedure Open_Read_Write (F : in out S_File) with
     Pre'Class  => F.Closed,
     Post'Class => F.Is_Open and F.Is_Writable,
     Global     => null,
     Always_Terminates;

   procedure Close (F : in out S_File) with
     Pre'Class  => F.Is_Open,
     Post'Class => F.Closed,
     Global     => null,
     Always_Terminates;

   function Closed (F : S_File) return Boolean with
     Global   => null;
   function Is_Open (F : S_File) return Boolean with
     Global   => null;
   function Is_Writable (F : S_File) return Boolean with
     Global   => null;
   function Is_Synchronized (F : S_File) return Boolean with
     Global   => null;

private
   type State is (Closed, Open_Read, Open_Read_Write);

   type S_File is new File_System.File with record
      In_Synch : Boolean;
   end record with
     Predicate => File_System.File (S_File).Closed or In_Synch;

end Synchronized_File_System;
