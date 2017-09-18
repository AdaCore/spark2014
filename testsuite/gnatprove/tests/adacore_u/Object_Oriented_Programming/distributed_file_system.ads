with File_System;

package Distributed_File_System
  with SPARK_Mode
is
   type File is new File_System.File with private;

   procedure Create (F : out File) with
     Post'Class => F.Closed;

   procedure Open_Read (F : in out File) with
     Pre'Class  => F.Closed,
     Post'Class => F.Is_Open and F.Is_Synchronized;

   procedure Open_Read_Write (F : in out File) with
     Pre'Class  => F.Closed,
     Post'Class => F.Is_Open and F.Is_Writable and F.Is_Synchronized;

   procedure Close (F : in out File) with
     Pre'Class  => F.Is_Open and F.Is_Synchronized,
     Post'Class => F.Closed;

   function Closed (F : File) return Boolean;
   function Is_Open (F : File) return Boolean;
   function Is_Writable (F : File) return Boolean;
   function Is_Synchronized (F : File) return Boolean;

private
   type State is (Closed, Open_Read, Open_Read_Write);

   type File is new File_System.File with record
      In_Synch : Boolean;
   end record;

end Distributed_File_System;
