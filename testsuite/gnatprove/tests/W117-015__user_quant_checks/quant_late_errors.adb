
--  Errors about recursivity, coming late

procedure Quant_late_errors with SPARK_Mode is
   package With_Contains is
      type Container is null record
        with Iterable => (First       => First,
                          Next        => Next,
                          Has_Element => Has_Element,
                          Element     => Element,
                          Last        => Last,
                          Previous    => Previous);
      function First (X : Container) return Boolean
        with Post => True;
      function Next (X : Container; Y : Boolean) return Boolean
        with Post => True;
      function Has_Element (X : Container; Y : Boolean) return Boolean
        with Post => True;
      function Contains (X : Container; Y : Boolean) return Boolean
        with Post => True;
      function Element (X : Container; Y : Boolean) return Boolean
        with Post => True;
      pragma Annotate (GNATprove, Iterable_For_Proof, "contains", Contains);
      function Last (X : Container) return Boolean;
      function Previous (X : Container; Y : Boolean) return Boolean;
   end With_Contains;
   package body With_Contains is
      function First (X : Container) return Boolean is
        (for all Y of X => Y);
      function Next (X : Container; Y : Boolean) return Boolean is
        (for all Z of X => Y /= Z);
      function Has_Element (X : Container; Y : Boolean) return Boolean is
        (for some Z of X => Y = Z);
      function Element (X : Container; Y : Boolean) return Boolean is
        (for some Z of X => Y /= Z);
      function Last (X : Container) return Boolean is
        (for all Y of X => not (Y));
      function Previous (X : Container; Y : Boolean) return Boolean is
        (for some Z of X => Y /= Z);
      function Contains (X : Container; Y : Boolean) return Boolean is
         (for all Z of X => Y /= Z and then (for some T of X => Z /= T));
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
      function First (X : Container) return Boolean
        with Post => True;
      function Next (X : Container; Y : Boolean) return Boolean
        with Post => True;
      function Has_Element (X : Container; Y : Boolean) return Boolean
        with Post => True;
      function Get_Model (X : Container) return Model
        with Post => True;
      function Element (X : Container; Y : Boolean) return Boolean
        with Post => True;
      pragma Annotate (GNATprove, Iterable_For_Proof, "model", Get_Model);
      function Last (X : Container) return Boolean
        with Pre => False;
      function Previous (X : Container; Y : Boolean) return Boolean
        with Pre => False;
   end With_Model;
   package body With_Model is
      function First (X : Container) return Boolean is
        (for all Y of X => Y);
      function Next (X : Container; Y : Boolean) return Boolean is
        (for all Z of X => Y /= Z);
      function Has_Element (X : Container; Y : Boolean) return Boolean is
        (for some Z of X => Y = Z);
      function Element (X : Container; Y : Boolean) return Boolean is
        (for some Z of X => Y /= Z);
      function Last (X : Container) return Boolean is
        (for all Y of X => not (Y));
      function Previous (X : Container; Y : Boolean) return Boolean is
        (for some Z of X => Y /= Z);
      function Get_Model (X : Container) return Model is
         (if (for all Y in X => Y) then (null record) else (null record));
   end With_Model;
begin
   null;
end Quant_late_errors;
