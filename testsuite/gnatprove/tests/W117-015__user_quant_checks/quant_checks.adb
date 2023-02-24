procedure Quant_checks with SPARK_Mode is

   package Fine is
      type Container is null record
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      type Cursor is range 0 .. 2;
      function First (C : Container) return Cursor is (0);
      function Has_Element (C : Container; I : Cursor) return Boolean is
        (I /= 2);
      function Next (C : Container; I : Cursor) return Cursor is (I+1)
        with Pre => Has_Element (C, I);
      function Element (C : Container; I : Cursor) return Boolean is
        (I /= 0)
        with Pre => Has_Element (C, I);
   end Fine;
   
   package With_Contains is
      type Container is null record
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element,
                          Last        => Last,
                          Previous    => Previous);
      function First (X : Container) return Boolean is (False) --@PRECONDITION:FAIL
        with Pre => False;
      function Next (X : Container; Y : Boolean) return Boolean is (False) --@PRECONDITION:FAIL
        with Pre => False;
      function Has_Element (X : Container; Y : Boolean) return Boolean is (True) --@PRECONDITION:FAIL
        with Pre => False;
      function Contains (X : Container; Y : Boolean) return Boolean is (True) --@PRECONDITION:FAIL
        with Pre => False;
      function Element (X : Container; Y : Boolean) return Boolean is (False) --@PRECONDITION:FAIL
        with Pre => False;
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
      function Last (X : Container) return Boolean is (False)
        with Pre => False;
      function Previous (X : Container; Y : Boolean) return Boolean is (False)
        with Pre => False;
   end With_Contains;
   package With_Model is
      type Model is null record
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      function First (X : Model) return Integer is (0);
      function Next (X : Model; I : Integer) return Integer is
        (if I < 2 then I+1 else I);
      function Has_Element (X : Model; I : Integer) return Boolean is
        (I in 0 .. 1);
      function Element (X : Model; I : Integer) return Boolean is (I /= 0);
      type Container is null record
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element,
                          Last        => Last,
                          Previous    => Previous);
      function First (X : Container) return Boolean is (False) --@PRECONDITION:FAIL
        with Pre => False;
      function Next (X : Container; Y : Boolean) return Boolean is (False) --@PRECONDITION:FAIL
        with Pre => False;
      function Has_Element (X : Container; Y : Boolean) return Boolean is (True) --@PRECONDITION:FAIL
        with Pre => False;
      function Get_Model (X : Container) return Model is --@PRECONDITION:FAIL
        (null record)
        with Pre => False;
      function Element (X : Container; Y : Boolean) return Boolean is (False) --@PRECONDITION:FAIL
        with Pre => False;
      pragma Annotate (GNATprove, Iterable_For_Proof, "model", Get_Model);
      function Last (X : Container) return Boolean is (False)
        with Pre => False;
      function Previous (X : Container; Y : Boolean) return Boolean is (False)
        with Pre => False;
   end With_Model;
   package Slightly_Too_Strong is
      type Container is null record
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element);
      type Cursor is range 0 .. 2;
      function Unknown (I : Integer) return Boolean
        with Import, Global => null, Annotate => (GNATprove, Always_Return);
      function Has_Element (X : Container; I : Cursor) return Boolean
        with Import, Global => null, Annotate => (GNATprove, Always_Return);
      function First (X : Container) return Cursor is (0) --@PRECONDITION:FAIL
        with Pre =>
          Has_Element (X, 0)
          or else Has_Element (X, 1)
          or else Has_Element (X, 2)
          or else Unknown (0);
      function Next (X : Container; I : Cursor) return Cursor is (I+1) --@PRECONDITION:FAIL
        with Pre => Has_Element (X, I) and then Unknown (0);
      function Contains (X : Container; B : Boolean) return Boolean is (True) --@PRECONDITION:FAIL
        with Pre =>
          Has_Element (X, 0)
          or else Has_Element (X, 1)
          or else Has_Element (X, 2)
          or else Unknown (0);
      function Element (X : Container; I : Cursor) return Boolean is --@PRECONDITION:FAIL
        (I /= 0)
        with Pre =>
          Has_Element (X, I)
          and then Unknown (0);
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
   end Slightly_Too_Strong;

begin
   null;
end Quant_checks;
