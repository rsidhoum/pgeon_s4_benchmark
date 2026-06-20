all: 
	ocamlfind ocamlopt -package unix,str,findlib -linkpkg -o twbcompile twbcompile.ml

cgiclient:
	ocamlfind ocamlopt -package xmlrpc-light -linkpkg -o cgiclient cgiclient.ml

clean:
	rm -f cgiclient twbcompile *.cm* *.o
