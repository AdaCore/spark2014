package Lists with SPARK_Mode is

   type Index is range 1 .. 100;

   function Goes_To (I, J : Index) return Boolean;

   function Goes_To2 (I, J : Index) return Boolean;

   procedure Link (I, J : Index) with
     Post => Goes_To2 (I, J);

private

   type Cell (Is_Set : Boolean := True) is record
      case Is_Set is
         when True => Next : Index;
         when False => null;
      end case;
   end record;

   type Cell_Array is array (Index) of Cell;

   Memory1 : Cell_Array;

   function Goes_To2 (I, J : Index) return Boolean is
     (Memory1 (I).Is_Set and then Memory1 (I).Next = J);

end Lists;
