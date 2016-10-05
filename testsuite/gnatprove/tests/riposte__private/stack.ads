package Stack with SPARK_Mode is

   type Length_T is range 0 .. 100;

   type T is private;

   Null_Stack : constant T;

   function Get_Length (The_Stack : in T)
                       return Length_T;

   function Create_Stack return T
     with Post => Get_Length (Create_Stack'Result) = 0;

   function Top (The_Stack : in T) return Integer
      with Pre => Get_Length (The_Stack) > 0;

   procedure Push (The_Stack : in out T;
                   Elem      : in     Integer)
     with Depends => (The_Stack =>+ Elem),
          Pre     => Get_Length (The_Stack) < Length_T'Last,
          Post    => Get_Length (The_Stack) = Get_Length (The_Stack'Old) + 1
                       and Top (The_Stack) = Elem;

private
   subtype Pointer_T is Length_T range 1 .. Length_T'Last;

   type Array_T is array (Pointer_T) of Integer;

   type T is record
      Len      : Length_T;
      Elements : Array_T;
   end record;

   Null_Stack : constant T := T'(Len      => 0,
                                 Elements => Array_T'(others => Integer'First));
end Stack;
