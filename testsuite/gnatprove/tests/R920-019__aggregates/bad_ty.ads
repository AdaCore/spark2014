with Ext;
package Bad_Ty is
    type Root is tagged null record;
    type C is new Root with private;
    function F return Integer;
private

    type C is new Root with record
       F : Integer := Ext.V;
    end record;

    Cst : constant C := (F => 1);
    function F return Integer is (Cst.F);
end Bad_Ty;
