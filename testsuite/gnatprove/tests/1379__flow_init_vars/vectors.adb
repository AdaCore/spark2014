package body Vectors is

   ------------
   -- Delete --
   ------------

   procedure Delete (Container : in out Vector; Index : Natural) is
   begin
      Delete (Container, Index, 1);
   end Delete;

   procedure Delete
     (Container : in out Vector; Index : Natural; Count : Natural)
   is
   begin
      null;
   end Delete;

end Vectors;
