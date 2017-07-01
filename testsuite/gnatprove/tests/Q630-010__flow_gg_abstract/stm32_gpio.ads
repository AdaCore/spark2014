package STM32_GPIO is

   --------------------------------------------
   -- Base type and its abstract subprograms --
   --------------------------------------------

   type Base is limited interface;

   function Mode (This : Base) return Boolean is abstract;

   procedure Set (This : in out Base) is abstract
     with Pre'Class => This.Mode;

   -----------------------------------------------
   -- Derived type and its concrete subprograms --
   -----------------------------------------------

   type Derived is new Base with record
      Dummy : Integer; --  to not care about extension being null
   end record;

   overriding
   function Mode (This : Derived) return Boolean;

   overriding
   procedure Set (This : in out Derived);

end STM32_GPIO;
