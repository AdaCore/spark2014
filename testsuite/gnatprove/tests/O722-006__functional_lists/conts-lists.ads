--  This package provides various generic packages used for the implementation
--  of the various list containers.
--  It is in fact possible to customize the containers to change the way the
--  nodes are stored, for instance, although default implementations are
--  provided for bounded/unbounded containers, and constrained/unconstrained
--  elements.

pragma Ada_2012;
with Ada.Finalization; use Ada.Finalization;

package Conts.Lists is

   type Controlled_Base_List is abstract new Controlled with null record;
   type Limited_Base_List is abstract tagged limited null record;
   --  All lists have a common ancestor, although this cannot be used to
   --  reuse code. This base type is only needed so that we can implement
   --  bounded containers and still share the code.

   -----------------
   -- Node traits --
   -----------------
   --  The following packages are used to describe some types of nodes that
   --  can be used to build a list. We use a different type depending on
   --  whether we have a bounded or unbounded list, for instance. Other
   --  implementations are possible to adapt to existing data structures,
   --  for instance.

   generic
      with package Elements is new Elements_Traits (<>);
      --  The type of elements stored in nodes

      type Container (<>) is abstract tagged limited private;
      --  A container for all nodes.
      --  Such a container is not needed when nodes are allocated on the heap
      --  and accessed via pointers; but it is needed when nodes are stored in
      --  an array, for instance.
      --  This is used as the ancestor type for the list types.

      type Node_Access is private;
      --  Access to a node. This is either an actual pointer or an index into
      --  some other data structure.

      Null_Access : Node_Access;

      with procedure Allocate
         (Nodes : in out Container'Class;
          Element  : Elements.Stored_Element_Type;
          New_Node : out Node_Access);
      --  Allocate a new node, that contains Element. Its next and previous
      --  siblings have been initialized to Null_Access.
      --  This procedure can return Null_Access is the new node could not be
      --  allocated.

      with procedure Release_Node
         (Self : in out Container'Class; N : in out Node_Access) is <>;
      --  Free the memroy for a specific node.
      --  This function should not free the element itself, this has already
      --  been handled by the container (this is so that a null procedure can
      --  be passed in the common case).

      with procedure Release (Nodes : in out Container'Class) is <>;
      --  Free all the memory used by the container.
      --  This should not free the nodes themselves, this has already been
      --  taken care of by the container. This is so that a null procedure
      --  can be passed in the common case.

      with function Get_Element
         (Nodes    : Container'Class;
          Position : Node_Access) return Elements.Stored_Element_Type is <>;
      with function Get_Next
         (Nodes    : Container'Class;
          Position : Node_Access) return Node_Access is <>;
      with function Get_Previous
         (Nodes    : Container'Class;
          Position : Node_Access) return Node_Access is <>;
      --  Get the next and previous elements for a node

      with procedure Set_Next
         (Nodes    : in out Container'Class;
          Position : Node_Access;
          Next     : Node_Access) is <>;
      with procedure Set_Previous
         (Nodes    : in out Container'Class;
          Position : Node_Access;
          Previous : Node_Access) is <>;
      --  Change the next and previous elements for a node

      with function Capacity
         (Nodes    : Container'Class) return Count_Type is <>;
      --  How many nodes can be stored in Nodes

      with procedure Assign
         (Nodes    : in out Container'Class;
          Source   : Container'Class;
          New_Head : out Node_Access;
          Old_Head : Node_Access;
          New_Tail : out Node_Access;
          Old_Tail : Node_Access) is <>;
      --  Replace all nodes in Nodes with a copy of the nodes in Source.
      --  The elements themselves need to be copied (via Elements.Copy).

   package List_Nodes_Traits with SPARK_Mode is
      --  pragma Unreferenced (Null_Access, Allocate, Get_Element, Get_Next);
      --  pragma Unreferenced (Get_Previous, Set_Next, Set_Previous);
      --  ??? Other packages need those, but the compiler is complaining that
      --  these formal parameters are unused in this package.
   end List_Nodes_Traits;

   ------------------------
   -- Bounded list nodes --
   ------------------------
   --  Such nodes are implemented via an array, so that no dynamic memory
   --  allocation is needed

   generic
      with package Elements is new Elements_Traits (<>);
      type Controlled_Or_Limited is abstract tagged limited private;
   package Bounded_List_Nodes_Traits with SPARK_Mode is

      subtype Stored_Element_Type is Elements.Stored_Element_Type;

      type Node_Access is new Count_Type;
      Null_Node_Access : constant Node_Access := 0;
      type Node is record
         Element        : Stored_Element_Type;
         Previous, Next : Node_Access := Null_Node_Access;
      end record;

      type Nodes_Array is array (Count_Type range <>) of Node;

      type Nodes_List (Capacity : Count_Type) is
         abstract new Controlled_Or_Limited
      with record
         Nodes : Nodes_Array (1 .. Capacity);

         Free  : Integer := 0;   --  head of free nodes list
         --  For a negative value, its absolute value points to the first free
         --  element
      end record;

      procedure Allocate
         (Self    : in out Nodes_List'Class;
          Element : Stored_Element_Type;
          N       : out Node_Access);   --  not inlined
      procedure Release (Self : in out Nodes_List'Class) is null;
      procedure Release_Node
         (Self : in out Nodes_List'Class; N : in out Node_Access) is null;
      function Get_Element
         (Self : Nodes_List'Class; N : Node_Access) return Stored_Element_Type
         is (Self.Nodes (Count_Type (N)).Element);
      function Get_Next
         (Self : Nodes_List'Class; N : Node_Access) return Node_Access
         is (Self.Nodes (Count_Type (N)).Next);
      function Get_Previous
         (Self : Nodes_List'Class; N : Node_Access) return Node_Access
         is (Self.Nodes (Count_Type (N)).Previous);
      procedure Set_Next
         (Self : in out Nodes_List'Class; N, Next : Node_Access);
      procedure Set_Previous
         (Self : in out Nodes_List'Class; N, Previous : Node_Access);
      function Capacity
         (Self : Nodes_List'Class) return Count_Type
         is (Self.Capacity);
      procedure Assign
         (Nodes    : in out Nodes_List'Class;
          Source   : Nodes_List'Class;
          New_Head : out Node_Access;
          Old_Head : Node_Access;
          New_Tail : out Node_Access;
          Old_Tail : Node_Access);
      pragma Inline (Set_Next, Set_Previous, Capacity);
      pragma Inline (Get_Element, Get_Next, Get_Previous);

      package Nodes is new List_Nodes_Traits
         (Elements     => Elements,
          Container    => Nodes_List,
          Node_Access  => Node_Access,
          Null_Access  => Null_Node_Access,
          Allocate     => Allocate);
   end Bounded_List_Nodes_Traits;

   --------------------------
   -- Unbounded_List_Nodes --
   --------------------------
   --  Such nodes are implemented via standard access types.
   --  The cursors are also direct access types to the data.

   generic
      with package Elements is new Elements_Traits (<>);
      type Controlled_Or_Limited is abstract tagged limited private;
   package Unbounded_List_Nodes_Traits with SPARK_Mode => Off is

      subtype Nodes_Container is Controlled_Or_Limited;
      --  type Nodes_Container is null record;
      type Node;
      type Node_Access is access Node;
      type Node is record
         Element        : Elements.Stored_Element_Type;
         Previous, Next : Node_Access;
      end record;

      procedure Allocate
         (Self    : in out Nodes_Container'Class;
          Element : Elements.Stored_Element_Type;
          N       : out Node_Access);
      procedure Release (Self : in out Nodes_Container'Class) is null;
      procedure Release_Node
         (Self : in out Nodes_Container'Class; N : in out Node_Access);
      function Get_Element
         (Self : Nodes_Container'Class; N : Node_Access)
         return Elements.Stored_Element_Type
         is (N.Element);
      function Get_Next
         (Self : Nodes_Container'Class; N : Node_Access) return Node_Access
         is (N.Next);
      function Get_Previous
         (Self : Nodes_Container'Class; N : Node_Access) return Node_Access
         is (N.Previous);
      procedure Set_Next
         (Self : in out Nodes_Container'Class; N, Next : Node_Access);
      procedure Set_Previous
         (Self : in out Nodes_Container'Class; N, Previous : Node_Access);
      function Capacity (Self : Nodes_Container'Class) return Count_Type
         is (Count_Type'Last);
      procedure Assign
         (Nodes    : in out Nodes_Container'Class;
          Source   : Nodes_Container'Class;
          New_Head : out Node_Access;
          Old_Head : Node_Access;
          New_Tail : out Node_Access;
          Old_Tail : Node_Access);
      pragma Inline (Allocate, Set_Next, Set_Previous, Capacity);
      pragma Inline (Get_Element, Get_Next, Get_Previous);

      package Nodes is new List_Nodes_Traits
         (Elements       => Elements,
          Container      => Nodes_Container,
          Node_Access    => Node_Access,
          Null_Access    => null,
          Allocate       => Allocate);
   end Unbounded_List_Nodes_Traits;

   --------------------------------
   -- SPARK Unbounded list nodes --
   --------------------------------
   --  For unbounded containers, SPARK uses an array of access
   --  types. Cursors are indexes into this array, so that the same cursor
   --  can be used both before and after a change (post-conditions), and to
   --  make them safer.

   generic
      with package Elements is new Elements_Traits (<>);
      type Controlled_Or_Limited is abstract tagged limited private;
   package SPARK_Unbounded_List_Nodes_Traits with SPARK_Mode is

      type Node_Access is new Count_Type;
      Null_Node_Access : constant Node_Access := 0;
      type Node is record
         Element        : Elements.Stored_Element_Type;
         Previous, Next : Node_Access := Null_Node_Access;
      end record;

      type Big_Nodes_Array is array (1 .. Count_Type'Last) of Node;
      package Private_Nodes_List with SPARK_Mode is
         type Nodes_List is abstract new Controlled_Or_Limited with private;

         procedure Allocate
           (Self    : in out Nodes_List'Class;
            Element : Elements.Stored_Element_Type;
            N       : out Node_Access);   --  not inlined
         procedure Release (Self : in out Nodes_List'Class);
         procedure Release_Node
           (Self : in out Nodes_List'Class; N : in out Node_Access) is null;
         function Get_Element
           (Self : Nodes_List'Class; N : Node_Access)
          return Elements.Stored_Element_Type;
         function Get_Next
           (Self : Nodes_List'Class; N : Node_Access) return Node_Access;
         function Get_Previous
           (Self : Nodes_List'Class; N : Node_Access) return Node_Access;
         procedure Set_Next
           (Self : in out Nodes_List'Class; N, Next : Node_Access);
         procedure Set_Previous
           (Self : in out Nodes_List'Class; N, Previous : Node_Access);
         function Capacity (Self : Nodes_List'Class) return Count_Type
         is (Count_Type'Last);
         procedure Assign
           (Nodes    : in out Nodes_List'Class;
            Source   : Nodes_List'Class;
            New_Head : out Node_Access;
            Old_Head : Node_Access;
            New_Tail : out Node_Access;
            Old_Tail : Node_Access);
         pragma Inline (Set_Next, Set_Previous, Capacity);
         pragma Inline (Get_Element, Get_Next, Get_Previous);
      private
         pragma SPARK_Mode (Off);
         type Nodes_Array_Access is access Big_Nodes_Array;
         for Nodes_Array_Access'Storage_Size use 0;
         --  The nodes is a pointer so that we can use realloc

         type Nodes_List is abstract new Controlled_Or_Limited with record
            Nodes : Nodes_Array_Access := null;
            Last  : Count_Type := 0;  --  Last valid index in Nodes
            Free  : Integer := 0;     --  head of free nodes list
            --  For a negative value, its absolute value points to the first
            --  free element
         end record;

         function Get_Element
           (Self : Nodes_List'Class; N : Node_Access)
          return Elements.Stored_Element_Type
         is (Self.Nodes (Count_Type (N)).Element);
         function Get_Next
           (Self : Nodes_List'Class; N : Node_Access) return Node_Access
         is (Self.Nodes (Count_Type (N)).Next);
         function Get_Previous
           (Self : Nodes_List'Class; N : Node_Access) return Node_Access
         is (Self.Nodes (Count_Type (N)).Previous);
      end Private_Nodes_List;

      use Private_Nodes_List;

      package Nodes is new List_Nodes_Traits
        (Elements     => Elements,
         Container    => Nodes_List,
         Node_Access  => Node_Access,
         Null_Access  => Null_Node_Access,
         Allocate     => Allocate);
   end SPARK_Unbounded_List_Nodes_Traits;

   -----------
   -- Lists --
   -----------
   --  A generic and general list implementation
   --  By providing appropriate values for the formal parameters, the same
   --  implementation can be used for bounded and unbounded containers, or for
   --  constrained and unconstrained elements.
   --
   --  Design: in C++ STL, none of the methods are virtual, so there is no
   --  dynamic dispatching. We achieve the same here by using 'Class
   --  parameters.  This still let's use Ada2012 dot notation (the reason why
   --  we use a tagged type, in addition to the Iterable aspect), while
   --  increasing the performance (the count-with-explicit-loop goes from 0.25s
   --  to 0.51s when we do not use 'Class parameters).

   generic
      with package Nodes is new List_Nodes_Traits (<>);

      Enable_Asserts : Boolean := False;
      --  If True, extra asserts are added to the code. Apart from them, this
      --  code runs with all compiler checks disabled.

   package Generic_Lists  with SPARK_Mode is
      type List is new Nodes.Container with private;
      --  We do not define the Iterable aspect here: this is not allowed,
      --  since the parent type is a generic formal parameter. Instead, we
      --  have to define it in the instantiations of Generic_List.

      subtype Element_Type is Nodes.Elements.Element_Type;
      subtype Reference_Type is Nodes.Elements.Reference_Type;
      subtype Stored_Element_Type is Nodes.Elements.Stored_Element_Type;
      type Cursor is private;

      procedure Append
         (Self    : in out List'Class;
          Element : Element_Type)
         with Global => null,
              Pre    => Length (Self) <= Capacity (Self) - 1;
      --  Append a new element to the list.
      --  Complexity: O(1)
      --  Raises: Storage_Error if Enable_Asserts is True and the node can't
      --     be allocated.

      function Length (Self : List'Class) return Count_Type
         with Inline => True,
              Global => null;
      --  Return the number of elements in the list.
      --  Complexity: O(n)  (in practice, constant)

      function Capacity (Self : List'Class) return Count_Type
         is (Nodes.Capacity (Self))
         with Inline => True,
              Global => null;
      --  Return the maximal number of elements in the list. This will be
      --  Count_Type'Last for unbounded containers.
      --  Complexity: constant

      procedure Clear (Self : in out List'Class);
      --  Free the contents of the list
      --  Complexity:  O(n)

      procedure Assign (Self : in out List'Class; Source : List'Class);
      --  Replace all elements of Self with a copy of the elements of Source.
      --  When the list is controlled, this has the same behavior as calling
      --  Self := Source.
      --  Complexity: O(n)

      function First (Self : List'Class) return Cursor
         with Inline => True,
              Global => null;
      function Element
         (Self : List'Class; Position : Cursor) return Element_Type
         with Inline => True,
              Global => null,
              Pre    => Has_Element (Self, Position);
      function Has_Element
         (Self : List'Class; Position : Cursor) return Boolean
         with Inline => True,
              Global => null;
      function Next
         (Self : List'Class; Position : Cursor) return Cursor
         with Inline => True,
              Global => null,
              Pre    => Has_Element (Self, Position);
      function Previous
         (Self : List'Class; Position : Cursor) return Cursor
         with Inline => True,
              Global => null,
              Pre    => Has_Element (Self, Position);
      --  We pass the container explicitly for the sake of writing the pre
      --  and post conditions.
      --  Complexity: constant for all cursor operations.

      function Stored_Element
         (Self : List'Class; Position : Cursor) return Stored_Element_Type
         with Inline => True,
              Global => null,
              Pre    => Has_Element (Self, Position);
      --  Accessing directly the stored element might be more efficient in a
      --  lot of cases.
      --  ??? Can we prevent users from freeing the pointer (when it is a
      --  pointer), or changing the element in place ?

      function Reference
         (Self : List'Class; Position : Cursor) return Reference_Type
         is (Nodes.Elements.Get_Reference
                (Stored_Element (Self, Position)))
         with Inline => True,
              Global => null,
              Pre    => Has_Element (Self, Position);

      procedure Next (Self : List'Class; Position : in out Cursor)
         with Inline => True,
              Global => null,
              Pre    => Has_Element (Self, Position);

      function First_Primitive (Self : List) return Cursor
         is (First (Self));
      function Element_Primitive
         (Self : List; Position : Cursor) return Element_Type
         is (Element (Self, Position));
      function Has_Element_Primitive
         (Self : List; Position : Cursor) return Boolean
         is (Has_Element (Self, Position));
      function Next_Primitive
         (Self : List; Position : Cursor) return Cursor
         is (Next (Self, Position));
      pragma Inline (First_Primitive, Element_Primitive);
      pragma Inline (Has_Element_Primitive, Next_Primitive);
      --  These are only needed because the Iterable aspect expects a parameter
      --  of type List instead of List'Class. But then it means that the loop
      --  is doing a lot of dynamic dispatching, and is twice as slow as a loop
      --  using an explicit cursor.

   private
      pragma SPARK_Mode (Off);
      procedure Adjust (Self : in out List);
      procedure Finalize (Self : in out List);
      --  In case the list is a controlled type, but irrelevant when the list
      --  is not controlled.

      type List is new Nodes.Container with record
         Head, Tail : Nodes.Node_Access := Nodes.Null_Access;
         Size : Natural := 0;
      end record;
      --  controlled just to check for performance for now.
      --  Formal containers should not use controlled types, but it might be
      --  necessary to implement some strategies like automatic memory handling
      --  or copy-on-assign for instance.

      type Cursor is record
         Current : Nodes.Node_Access;
      end record;
   end Generic_Lists;

   generic
      with package Lists is new Generic_Lists (<>);
      type List (<>) is new Lists.List with private;
   package List_Cursors with SPARK_Mode is
      --  Convenient package for creating the cursors traits for a list.
      --  These cursor traits cannot be instantiated in Generic_Lists itself,
      --  since the List type is frozen too late.
      --  We also assume that List might be a child of Lists.List, not the
      --  same type directly, so we need to have proxies for the cursor
      --  subprograms

      subtype Cursor is Lists.Cursor;
      subtype Element_Type is Lists.Nodes.Elements.Element_Type;
      subtype Reference_Type is Lists.Nodes.Elements.Reference_Type;
      subtype Stored_Element_Type is Lists.Nodes.Elements.Stored_Element_Type;

      function Cursors_First (Self : List'Class) return Cursor
         is (Lists.First (Self));
      function Cursors_Element
         (Self : List'Class; Position : Cursor) return Element_Type
         is (Lists.Element (Self, Position))
      with Pre => Lists.Has_Element (Self, Position);
      function Cursors_Stored_Element (Self : List'Class; Position : Cursor)
         return Stored_Element_Type
         is (Lists.Stored_Element (Self, Position))
      with Pre => Lists.Has_Element (Self, Position);
      function Cursors_Reference (Self : List'Class; Position : Cursor)
         return Reference_Type
         is (Lists.Reference (Self, Position))
      with Pre => Lists.Has_Element (Self, Position);
      function Cursors_Has_Element
         (Self : List'Class; Position : Cursor) return Boolean
         is (Lists.Has_Element (Self, Position));
      function Cursors_Next
         (Self : List'Class; Position : Cursor) return Cursor
         is (Lists.Next (Self, Position))
      with Pre => Lists.Has_Element (Self, Position);
      function Cursors_Previous
         (Self : List'Class; Position : Cursor) return Cursor
         is (Lists.Previous (Self, Position))
      with Pre => Lists.Has_Element (Self, Position);
      pragma Inline (Cursors_First, Cursors_Element, Cursors_Has_Element);
      pragma Inline (Cursors_Next, Cursors_Previous);

      package Bidirectional is new Bidirectional_Constant_Cursors_Traits
         (Container    => List'Class,
          Cursor       => Cursor,
          Element_Type => Element_Type,
          First        => Cursors_First,
          Next         => Cursors_Next,
          Has_Element  => Cursors_Has_Element,
          Element      => Cursors_Element,
          Previous     => Cursors_Previous);
      package Forward renames Bidirectional.Forward;

      package Bidirectional_Stored is new Bidirectional_Constant_Cursors_Traits
         (Container    => List'Class,
          Cursor       => Lists.Cursor,
          Element_Type => Stored_Element_Type,
          First        => Cursors_First,
          Next         => Cursors_Next,
          Has_Element  => Cursors_Has_Element,
          Element      => Cursors_Stored_Element,
          Previous     => Cursors_Previous);
      package Forward_Stored renames Bidirectional_Stored.Forward;
      --  Another version of cursors that manipulates the Element_Access. These
      --  might be more efficient.

      package Bidirectional_Reference
         is new Bidirectional_Constant_Cursors_Traits
         (Container    => List'Class,
          Cursor       => Lists.Cursor,
          Element_Type => Reference_Type,
          First        => Cursors_First,
          Next         => Cursors_Next,
          Has_Element  => Cursors_Has_Element,
          Element      => Cursors_Reference,
          Previous     => Cursors_Previous);
      package Forward_Reference renames Bidirectional_Reference.Forward;
      --  Another version of cursors that manipulates the Element_Access. These
      --  might be more efficient.

   end List_Cursors;
end Conts.Lists;
