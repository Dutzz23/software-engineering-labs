method Triple (x: int ) returns (r: int)
{
  var y := 2 * x;
  r := x + y;
}

method Caller() {
  var t := Triple (18); // => 54
  // assert t < 100; => eroare
}

method Triple2 (x: int ) returns (r: int)
{
  var y := 2 * x;
  r := x + y;
  assert r == 3 * x; 
  // assert r == 3 * x + 1 => eroare
}

method Triple3 (x: int ) returns (r: int)
{
  var y := 2 * x;
  r := x + y;
  assert r==3 * x; //assert r == 10 * x;
  //assert r < 5; => nu este relevanta verificarea. Nu stim destule informatii despre r
  //assert false ; => test nereusit indiferent de rezultat
}

method Triple4(x: int ) returns (r: int)
{
  if x == 0{
    r := 0; // => atribuire corecta
  } else {
    var y := 2 * x;
    r := x + y;
  }
  assert r == 3 * x;
}


method Caller4() {
  var t := Triple4(18) ; // => 54
  var v := Triple4(0);   // => 0
}

method Triple5 (x: int ) returns (r: int)
{
  if {
    case x < 18 =>
      var a, b := 2 * x, 4 * x;
      r := (a+b) / 2;
    case 0 <= x =>
      var y := 2 * x;
      r := x + y;
  }
  assert r == 3 * x;
}

method Caller5() {
  var t := Triple5(18) ; // => 54
  var v := Triple5(3);   // => 9
}


method Triple6 (x: int ) returns (r: int)
  ensures r == 3 * x // => postconditie satisfacuta
{
  var y := 2 * x;
  r := x + y;

}
method Triple7 (x: int ) returns (r: int)
  requires x % 2 == 0 // => r nu este neaparat de forma 3*x

  ensures r == 3 * x
{

  var y := x / 2;
  r := 6 * y;
}
// Postconditie =>  o conditie ce trebuie indeplinita inainte de executia algoritmului.
// In exemplul de mai sus, requires x % 2 == 0 asigura că metoda Triple este apelata doar cu numere pare,
// astfel incat x/2 returneaza un rezultat corect, in ciuda comportamentului operatiei asupra numerelor de tip intreg.

// Postconditie =>  o conditie ce trebuie indeplinita dupa executia algoritmului.
// Postcondiția ensures r == 3 * x asigura ca rezultatul, r, este de forma 3*x.

method Min(x: int , y: int ) returns (m: int )
  ensures m <= x && m <= y
{
  if x <= y {
    m := x;
  } else {
    m := y;
  }
}

method Minfake (x: int , y: int) returns (m: int )
  ensures m <= x && m <= y
{
  if x <= y {
    m := x - 10;
  } else {
    m := y - 20;
  }
}