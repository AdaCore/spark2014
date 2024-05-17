procedure Main with SPARK_Mode is

   package P is

      type Chars_Ptr is private with
        Default_Initial_Condition => Is_Null (Chars_Ptr);
      pragma Preelaborable_Initialization (Chars_Ptr);

      Null_Ptr : constant Chars_Ptr;

      --  We should start the copy here

      function Is_Null (Item : Chars_Ptr) return Boolean with
        Ghost,
        Post => Is_Null'Result = (Item = Null_Ptr);

      procedure Test;

   private
      type Chars_Ptr is access constant String;

      Null_Ptr : constant Chars_Ptr := null;

      function Is_Null (Item : Chars_Ptr) return Boolean is
        (Item = null);
   end P;

   package body P is

      function F1 (Item : Chars_Ptr) return String is
        (Item.all)
      with Pre => Item /= Null_Ptr;

      function F2 (Item : Chars_Ptr) return String
          with Pre => Item /= null
      is
      begin
        return F1 (Item);
      end F2;

      function F3 (Item : Chars_Ptr) return String
          with Pre => Item /= null
      is
         X : Chars_Ptr := Null_Ptr;
      begin
        return F1 (Item);
      end F3;

      procedure Test is null;

   end P;

begin
   null;
end Main;
