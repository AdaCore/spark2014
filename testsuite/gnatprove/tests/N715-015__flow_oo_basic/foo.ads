package Foo
is

   type Root_T is tagged null record;

   function Hash (Obj : Root_T) return Natural with
     Global   => null,
     Annotate => (GNATprove, Always_Return);

   --------------------------

   type Widget_T is new Root_T with record
      X, Y : Integer;
   end record;

   overriding function Hash (Obj : Widget_T) return Natural;
   procedure Zero_Widget (Obj : out Widget_T) with
     Global   => null,
     Annotate => (GNATprove, Always_Return);

   --------------------------

   type Nice_Widget_T is new Widget_T with record
      Round : Boolean;
   end record;

   overriding function Hash (Obj : Nice_Widget_T) return Natural;
   overriding procedure Zero_Widget (Obj : out Nice_Widget_T);

   --------------------------

   type Magic_Widget_T is new Widget_T with private;

   overriding procedure Zero_Widget (Obj : out Magic_Widget_T);
   overriding function Hash (Obj : Magic_Widget_T) return Natural;

   --------------------------

   Null_Widget : constant Widget_T := (0, 0);

   --------------------------

   type Misc_Private_T (Valid : Boolean) is private;

   procedure Modify_It (X : in out Misc_Private_T;
                        N : in     Integer)
   with
     Global   => null,
     Annotate => (GNATprove, Always_Return);

private

   type Magic_Widget_T is new Widget_T with record
      Magic : Boolean;
   end record;

   type Misc_Private_T (Valid : Boolean) is record
      case Valid is
         when True =>
            Field : Integer;
         when False =>
            null;
      end case;
   end record;

end Foo;
