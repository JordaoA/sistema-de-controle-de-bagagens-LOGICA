/*Descrição:  No aeroporto Flying To Heaven, foi solicitado um novo sistema para controle de bagagens.
 O mesmo consiste em verificar, durante a esteira do aeroporto, se o passageiro excedeu o limite de 
bagagem. Para isso, foi necessário classificar os passageiros e as bagagens. O passageiro pode ser 
de três tipos:  comum, milhagem ou VIP; e cada mala desse passageiro também possui três 
classificações: leve, mediana ou pesada. Além disso, o passageiro terá um ticket, que pode ser 
vermelho ou verde, indicando se ele pode embarcar.

O sistema irá considerar alguns parâmetros para verificar se o passageiro excedeu o limite:  

    Depois de verificar os pertences do passageiro, o tipo dele terá que ser considerado: Se ele for um 
passageiro comum, o mesmo só terá direito a no máximo uma bagagem pesada e uma leve, enquanto 
o passageiro milhagem tem como limite uma mala pesada, uma mediana e uma leve, entretanto, se for 
um VIP, terá como direito até duas pesadas, duas medianas e uma leve. 

Caso as condições não sejam satisfeitas, o passageiro não poderá embarcar e terá o ticket vermelho. 
Se não houver nenhum problema, o ticket terá que ser verde, significando que está apto a embarcar.

Cliente: Tiberio*/

module gerenciaDeBagagens

sig tipo{}

sig ticket{
	donoTk : one passageiro
}
	
sig bagagem{
	donoBg : one passageiro
}

/*
sig bagagemLeve extends bagagem{}
sig bagagemMediana extends bagagem{}
sig bagagemPesada extends bagagem{}
*/

sig passageiro{
	bagagemPas : set bagagem,
	ticketPas : one ticket
}

sig passageiroComun extends passageiro{}

sig passageiroMilhagem extends passageiro{}

sig passageiroVip extends passageiro{}



---FACTS---
fact passageiroF {
	some q: passageiro | some q.bagagemPas || no q.bagagemPas
}

fact bagagemF {
	some b: bagagem | one b.donoBg
	some b: bagagem, p: passageiro | b in p.bagagemPas 
}

fact ticketF {
	all t: ticket, p: passageiro | p in t.donoTk and t in p.ticketPas
}

pred show[]{}
run show for 5
