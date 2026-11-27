# AxiomWeave 논리 명세 (Logic Specification)

> **문서 상태:** 초안(Draft) · 단편 L0 · 대상 버전 v0.1  
> 상위 문서: [specification.md](specification.md). 이 문서는 AxiomCore 커널이 수용하는 타입, 항, 판단, 추론 규칙, 공리 체계를 정의한다. 규범적 표현은 [specification.md §1.1](specification.md#11-규범적-표현)을 따른다.

## 1. 범위

이 문서는 단순 타입 이론(Simple Type Theory)을 기반으로 한 논리 체계 중 **단편 L0(직관주의 명제 논리)** 를 정의한다.

| 포함                                         | 제외 (후속 단편)                           |
| -------------------------------------------- | ------------------------------------------ |
| 타입 $\mathsf{Prop}$과 논리 연산자 상수의 타입 | 람다 추상, 변수 바인딩 (L1)                |
| 명제 원자와 원시 연산자로 구성된 명제        | 양화사 (L1), 등식 (L2), 자연수 (L3)        |
| 자연 연역 추론 규칙                          | 사용자 정의(Definition) 선언과 δ-전개 (L1) |
| 정리·공리의 균일 치환 인스턴스화             | β·η 변환 (L1)                              |
| 공리 스키마와 고전 원리의 등록 방식          | 증명 객체의 직렬화 형식 (`kernel-spec.md`) |

증명 객체의 구체 인코딩, 이름 표현, 검증 알고리즘은 [kernel-spec.md](kernel-spec.md)에서 정의한다. 이 문서는 커널이 **무엇을** 인정해야 하는지를 정의하고, **어떻게** 검사하는지는 정의하지 않는다.

## 2. 설계 결정 요약

[specification.md §9](specification.md#9-미결-사항)에서 이 문서에 위임한 항목은 다음과 같이 확정한다.

| 항목                                                 | 결정                                                                       | 근거                                               |
| ---------------------------------------------------- | -------------------------------------------------------------------------- | -------------------------------------------------- |
| β·η 변환, δ-전개                                     | L0에 포함하지 않는다. 항의 동등성은 구문적 동일성이다.                     | L0 항에는 바인더와 정의가 없다.                    |
| 파생 연산자 ($\lnot$, $\top$, $\leftrightarrow$)     | 커널 밖의 축약 표기이며, 커널 입력 전에 원시 연산자로 완전히 전개한다.     | 커널의 신뢰 범위를 최소화한다.                     |
| 정의(Definition) 선언                                | L0 환경에서 지원하지 않는다.                                               | δ-전개 없이 정의는 의미가 없다.                    |
| 가정 이름                                            | 도입 시 신선한 이름이어야 하며 가림(Shadowing)을 허용하지 않는다.          | 가정 참조 검사를 단순화한다.                       |
| 약화 (Weakening)                                     | 별도 규칙 없이 $\mathrm{Hyp}$ 규칙에 내장한다.                             | 규칙 수를 최소화한다.                              |
| 정리 재사용                                          | 정리와 공리는 명제 원자에 대해 스키마적이며, 균일 치환으로 인스턴스화한다. | L0에는 명제 양화가 없다.                           |
| 고전 원리                                            | 이름 있는 공리 스키마로 등록하며, 동일한 인스턴스화 규칙을 사용한다.       | 기본 규칙을 직관주의로 유지하고 의존성을 추적한다. |

## 3. 타입과 항

### 3.1. 타입

$$
\begin{array}{rcl}
\tau & ::= & \mathsf{Prop} \mid \tau \to \tau
\end{array}
$$

L0에서 사용되는 타입은 $\mathsf{Prop}$과, 원시 연산자 상수에 부여되는 $\mathsf{Prop} \to \mathsf{Prop} \to \mathsf{Prop}$뿐이다. 함수 타입 구성자 $\to$는 우결합이다 ($\mathsf{Prop} \to \mathsf{Prop} \to \mathsf{Prop} = \mathsf{Prop} \to (\mathsf{Prop} \to \mathsf{Prop})$).

타입 수준의 $\to$와 명제 수준의 함의 상수 $\to$는 서로 다른 기호이다. 혼동이 우려되는 곳에서는 함의 상수를 $\mathsf{imp}$로 표기한다.

### 3.2. 시그니처

L0 시그니처 $\Sigma_0$는 다음 원시 상수로 구성된다.

| 상수           | 타입                                                  | 다른 표기            |
| -------------- | ----------------------------------------------------- | -------------------- |
| $\bot$         | $\mathsf{Prop}$                                       | `false`, `Falsehood` |
| $\mathsf{and}$ | $\mathsf{Prop} \to \mathsf{Prop} \to \mathsf{Prop}$ | $\land$, `And`       |
| $\mathsf{or}$  | $\mathsf{Prop} \to \mathsf{Prop} \to \mathsf{Prop}$ | $\lor$, `Or`         |
| $\mathsf{imp}$ | $\mathsf{Prop} \to \mathsf{Prop} \to \mathsf{Prop}$ | $\to$, `Implies`     |

- 원시 상수의 이름은 예약어이며, 명제 원자의 이름으로 사용해서는 안 된다.
- $\Sigma_0$에 상수를 추가하거나 타입을 변경하려면 이 문서를 개정해야 한다.

### 3.3. 명제 원자

명제 원자(Propositional Atom)는 타입 $\mathsf{Prop}$을 갖는 이름이다. 원자의 집합 $\mathcal{A}$는 가산 무한이며, 원자는 환경에 미리 선언하지 않고 사용할 수 있다.

- 원자는 해석이 고정되지 않은 명제를 나타낸다. 이 성질은 [6. 치환과 인스턴스화](#6-치환과-인스턴스화)의 근거가 된다.
- 원자 이름의 구문(허용 문자, 네임스페이스)은 [kernel-spec.md](kernel-spec.md)에서 정의한다.
- [specification.md §4.2](specification.md#42-v01-구현-대상-직관주의-명제-논리)의 "명제 변수"는 이 문서의 명제 원자를 뜻한다. L0에는 바인딩되는 변수가 없으므로 원자는 자유 변수도, 바인딩된 변수도 아니다.

### 3.4. 항

L0 항은 바인더와 변수가 없는 단순 타입 이론의 항이다.

$$
\begin{array}{rcll}
t & ::= & p & (p \in \mathcal{A}) \\
  & \mid & c & (c \in \Sigma_0) \\
  & \mid & t\ t & (\text{적용})
\end{array}
$$

**타입 규칙**

$$
\dfrac{p \in \mathcal{A}}{p : \mathsf{Prop}}\,(\mathrm{Atom})
\qquad\qquad
\dfrac{c : \tau \in \Sigma_0}{c : \tau}\,(\mathrm{Const})
\qquad\qquad
\dfrac{s : \tau_1 \to \tau_2 \qquad t : \tau_1}{s\ t : \tau_2}\,(\mathrm{App})
$$

**정의 (명제).** 항 $A$가 $A : \mathsf{Prop}$을 만족하면 $A$를 L0 명제라 한다. 판단 $A\ \mathsf{prop}$은 $A : \mathsf{Prop}$의 약어이다.

이 정의에 따라 다음이 성립한다.

- 모든 L0 명제는 원자, $\bot$, 또는 원시 연산자를 정확히 두 인자에 적용한 항이다. 부분 적용 항(예: $\mathsf{and}\ P$)은 타입이 $\mathsf{Prop} \to \mathsf{Prop}$이므로 명제가 아니다.
- 타입이 맞지 않는 항(예: $\mathsf{and}\ P\ Q\ R$, $P\ Q$)은 타입을 갖지 않으며, 커널은 이를 거부해야 한다.
- 람다 추상, 바운드 변수, $\mathsf{Prop}$ 이외의 기본 타입, $\Sigma_0$ 밖의 상수를 포함한 항은 L0 항이 아니며, 커널은 이를 단편 위반으로 거부해야 한다.

### 3.5. 표기 규약

이 문서와 하위 문서는 다음 중위 표기를 사용한다. 표기는 항의 구조를 바꾸지 않는다.

| 표기            | 항                   |
| --------------- | -------------------- |
| $A \land B$     | $\mathsf{and}\ A\ B$ |
| $A \lor B$      | $\mathsf{or}\ A\ B$  |
| $A \to B$       | $\mathsf{imp}\ A\ B$ |

결합 우선순위는 $\land$ > $\lor$ > $\to$ 이며, $\to$는 우결합이다. 예: $P \land Q \to R \lor S \to T = (P \land Q) \to ((R \lor S) \to T)$. 우선순위는 표기 규약일 뿐이며 커널은 트리 구조만 다룬다.

### 3.6. 항의 동등성

L0 항 $s$, $t$의 동등성 $s \equiv t$는 구문적 동일성이다. 즉, 같은 생성 규칙으로 같은 원자·상수로부터 같은 순서로 구성된 경우에만 동등하다.

- L0 항에는 바인더가 없으므로 α-동치는 구문적 동일성과 일치한다.
- L0 항에는 람다 추상과 정의가 없으므로 β·η·δ 변환은 적용 대상이 없다.
- 커널은 $\equiv$ 외의 동등성(예: 교환법칙, 결합법칙, 축약 표기 전개)을 사용해서는 안 된다.

## 4. 축약 표기

다음 연산자는 메타언어의 축약 표기이며 L0 항이 아니다.

| 표기                   | 전개 결과                         |
| ---------------------- | --------------------------------- |
| $\lnot A$              | $A \to \bot$                      |
| $\top$                 | $\bot \to \bot$                   |
| $A \leftrightarrow B$  | $(A \to B) \land (B \to A)$       |

- 축약 표기는 Elaborator 등 커널 바깥에서 커널 입력 전에 완전히 전개해야 한다.
- 커널은 축약 표기를 입력으로 받아서는 안 되며, 받은 경우 L0 항이 아니므로 거부해야 한다.
- 전개는 구조적으로 재귀적이다. 예: $\lnot\lnot A = (A \to \bot) \to \bot$.
- 출력 시 원시 항을 축약 표기로 다시 표시하는 것은 비신뢰 계층에서 할 수 있으며, 검증 결과에 영향을 주어서는 안 된다.
- $\lnot$의 우선순위는 $\land$보다 높다. $\leftrightarrow$의 우선순위는 $\to$보다 낮고 비결합이다.

## 5. 문맥과 판단

### 5.1. 문맥

문맥 $\Gamma$는 가정 이름과 명제의 유한한 순서 목록이다.

$$
\begin{array}{rcl}
\Gamma & ::= & \cdot \mid \Gamma, h : A
\end{array}
$$

**정의 (문맥 적격성).** 다음을 만족하면 $\Gamma$는 적격(Well-formed)하다.

1. $\Gamma$의 모든 명제 $A$에 대해 $A\ \mathsf{prop}$이 성립한다.
2. $\Gamma$의 가정 이름은 서로 다르다.

- $\mathrm{dom}(\Gamma)$는 $\Gamma$의 가정 이름 집합이다.
- $h : A \in \Gamma$는 $\Gamma$가 이름 $h$에 명제 $A$를 대응시킨다는 뜻이다. 적격 문맥에서 이 대응은 유일하다.
- 가정 이름의 구문은 [kernel-spec.md](kernel-spec.md)에서 정의한다. 가정 이름과 명제 원자는 서로 다른 이름 공간에 속한다.

### 5.2. 판단

| 판단                   | 의미                                                  |
| ---------------------- | ----------------------------------------------------- |
| $A\ \mathsf{prop}$     | $A$는 L0 명제이다 ([3.4](#34-항))                     |
| $\Gamma\ \mathsf{ctx}$ | $\Gamma$는 적격 문맥이다 ([5.1](#51-문맥))            |
| $E\ \mathsf{env}$      | $E$는 적격 환경이다 ([7.2](#72-환경-적격성))          |
| $E; \Gamma \vdash A$   | 환경 $E$와 문맥 $\Gamma$에서 명제 $A$가 도출된다      |

판단 $E; \Gamma \vdash A$는 $E\ \mathsf{env}$, $\Gamma\ \mathsf{ctx}$, $A\ \mathsf{prop}$을 전제로 한다. 환경이 문맥상 분명하면 $\Gamma \vdash A$로 줄여 쓴다.

## 6. 치환과 인스턴스화

### 6.1. 치환

치환(Substitution) $\sigma$는 명제 원자에서 L0 명제로 가는 유한 부분 함수이다.

$$
\sigma = [p_1 \mapsto B_1, \ldots, p_n \mapsto B_n] \qquad (p_i\ \text{는 서로 다른 원자, 각 } B_i\ \mathsf{prop})
$$

명제 $A$에 대한 치환 적용 $A[\sigma]$는 다음과 같이 **동시에** 정의한다.

$$
\begin{array}{lcll}
p[\sigma] & = & \sigma(p) & (p \in \mathrm{dom}(\sigma)) \\
p[\sigma] & = & p & (p \notin \mathrm{dom}(\sigma)) \\
\bot[\sigma] & = & \bot & \\
(c\ A\ B)[\sigma] & = & c\ A[\sigma]\ B[\sigma] & (c \in \lbrace \mathsf{and}, \mathsf{or}, \mathsf{imp} \rbrace)
\end{array}
$$

- 치환은 동시 치환이다. 예: $(P \to Q)[P \mapsto Q, Q \mapsto P] = Q \to P$.
- L0 항에는 바인더가 없으므로 변수 포획(Capture)은 발생하지 않는다.
- $A\ \mathsf{prop}$이고 $\sigma$의 모든 값이 명제이면 $A[\sigma]\ \mathsf{prop}$이다.

### 6.2. 원자 집합

$\mathrm{atoms}(A)$는 $A$에 나타나는 명제 원자의 집합이다.

$$
\begin{array}{lcl}
\mathrm{atoms}(p) & = & \lbrace p \rbrace \\
\mathrm{atoms}(\bot) & = & \emptyset \\
\mathrm{atoms}(c\ A\ B) & = & \mathrm{atoms}(A) \cup \mathrm{atoms}(B)
\end{array}
$$

### 6.3. 인스턴스화 조건

선언된 명제 $A$의 인스턴스화에 사용하는 치환 $\sigma$는 $\mathrm{dom}(\sigma) \subseteq \mathrm{atoms}(A)$를 만족해야 한다. 이 조건을 위반한 치환은 결과 명제와 무관하게 거부해야 한다.

이 조건은 결과에 영향을 주지 않는 치환 항목을 오류로 처리하여, 증명 생성기의 실수를 조기에 드러내기 위한 것이다. 치환에 나타나지 않은 원자는 그대로 유지된다.

## 7. 환경

### 7.1. 선언

환경 $E$는 선언의 유한한 순서 목록이다.

$$
\begin{array}{rcl}
E & ::= & \cdot \mid E, \mathsf{axiom}\ n : A \mid E, \mathsf{theorem}\ n : A
\end{array}
$$

| 선언                        | 의미                                                                    |
| --------------------------- | ----------------------------------------------------------------------- |
| $\mathsf{axiom}\ n : A$     | 이름 $n$의 공리 스키마. 증명 없이 $A$의 모든 인스턴스를 인정한다.       |
| $\mathsf{theorem}\ n : A$   | 이름 $n$의 정리. $A$의 증명이 커널에서 검증되어야 환경에 추가된다.      |

- 선언된 명제 $A$의 원자는 모두 스키마 변수로 해석한다. 즉 선언은 $\mathrm{atoms}(A)$에 대한 모든 균일 치환 인스턴스를 대표한다.
- L0 환경은 정의(Definition) 선언을 포함하지 않는다.

### 7.2. 환경 적격성

다음을 만족하면 $E$는 적격하다.

1. 빈 환경 $\cdot$은 적격하다.
2. $E\ \mathsf{env}$, $A\ \mathsf{prop}$, $n$이 $E$에 선언되지 않은 이름이면 $E, \mathsf{axiom}\ n : A$는 적격하다. 단, 해당 공리가 [8.3](#83-공리-허용-정책)의 허용 정책을 만족해야 한다.
3. $E\ \mathsf{env}$, $A\ \mathsf{prop}$, $n$이 $E$에 선언되지 않은 이름이고 $E; \cdot \vdash A$이면 $E, \mathsf{theorem}\ n : A$는 적격하다.

정리는 자신보다 앞에 선언된 공리와 정리만 사용할 수 있다. 따라서 적격 환경에는 순환 참조가 존재할 수 없다.

## 8. 추론 규칙

### 8.1. 규칙

아래의 모든 규칙에서 $E\ \mathsf{env}$, 결론의 $\Gamma\ \mathsf{ctx}$, 등장하는 모든 명제의 $A\ \mathsf{prop}$이 전제된다.

**가정**

$$
\dfrac{h : A \in \Gamma}{E; \Gamma \vdash A}\,(\mathrm{Hyp})
$$

**논리곱**

$$
\dfrac{E; \Gamma \vdash A \qquad E; \Gamma \vdash B}{E; \Gamma \vdash A \land B}\,(\land\mathrm{I})
\qquad\qquad
\dfrac{E; \Gamma \vdash A \land B}{E; \Gamma \vdash A}\,(\land\mathrm{E}_1)
\qquad\qquad
\dfrac{E; \Gamma \vdash A \land B}{E; \Gamma \vdash B}\,(\land\mathrm{E}_2)
$$

**논리합**

$$
\dfrac{E; \Gamma \vdash A}{E; \Gamma \vdash A \lor B}\,(\lor\mathrm{I}_1)
\qquad\qquad
\dfrac{E; \Gamma \vdash B}{E; \Gamma \vdash A \lor B}\,(\lor\mathrm{I}_2)
$$

$$
\dfrac{E; \Gamma \vdash A \lor B \qquad E; \Gamma, h_1 : A \vdash C \qquad E; \Gamma, h_2 : B \vdash C}{E; \Gamma \vdash C}\,(\lor\mathrm{E}) \quad h_1, h_2 \notin \mathrm{dom}(\Gamma)
$$

**함의**

$$
\dfrac{E; \Gamma, h : A \vdash B}{E; \Gamma \vdash A \to B}\,(\to\mathrm{I}) \quad h \notin \mathrm{dom}(\Gamma)
$$

$$
\dfrac{E; \Gamma \vdash A \to B \qquad E; \Gamma \vdash A}{E; \Gamma \vdash B}\,(\to\mathrm{E})
$$

**거짓**

$$
\dfrac{E; \Gamma \vdash \bot}{E; \Gamma \vdash A}\,(\bot\mathrm{E})
$$

**인스턴스화**

$$
\dfrac{\mathsf{theorem}\ n : A \in E \qquad \mathrm{dom}(\sigma) \subseteq \mathrm{atoms}(A)}{E; \Gamma \vdash A[\sigma]}\,(\mathrm{Thm})
$$

$$
\dfrac{\mathsf{axiom}\ n : A \in E \qquad \mathrm{dom}(\sigma) \subseteq \mathrm{atoms}(A)}{E; \Gamma \vdash A[\sigma]}\,(\mathrm{Ax})
$$

규칙은 위의 자연 연역 규칙 10개($\mathrm{Hyp}$, $\land\mathrm{I}$, $\land\mathrm{E}_1$, $\land\mathrm{E}_2$, $\lor\mathrm{I}_1$, $\lor\mathrm{I}_2$, $\lor\mathrm{E}$, $\to\mathrm{I}$, $\to\mathrm{E}$, $\bot\mathrm{E}$)와 인스턴스화 규칙 2개($\mathrm{Thm}$, $\mathrm{Ax}$)이며, 커널은 이 외의 추론을 허용해서는 안 된다. $\mathrm{Thm}$과 $\mathrm{Ax}$는 형태가 같지만 의존성 추적을 위해 구분한다.

### 8.2. 가정 이름 규칙

- $\to\mathrm{I}$와 $\lor\mathrm{E}$에서 도입하는 가정 이름은 결론 문맥 $\Gamma$에 없는 신선한 이름이어야 한다. 이미 $\mathrm{dom}(\Gamma)$에 있는 이름을 도입하는 도출은 거부해야 한다.
- $\lor\mathrm{E}$의 두 분기는 서로 독립이므로 $h_1$과 $h_2$는 같은 이름일 수 있다.
- 도입된 가정은 해당 규칙의 전제 도출 안에서만 사용할 수 있다. 규칙의 결론에서는 해제되어 문맥에 남지 않는다.
- 정리 $\mathsf{theorem}\ n : A$의 증명은 빈 문맥 $\cdot$에서 시작해야 한다. 따라서 해제되지 않은 가정에 의존하는 도출은 정리로 등록될 수 없다.

### 8.3. 공리 허용 정책

공리 스키마는 원자가 스키마 변수이므로 매우 강력하다. 예를 들어 $\mathsf{axiom}\ \mathrm{bad} : P$를 허용하면 $\mathrm{Ax}$로 $P[P \mapsto \bot] = \bot$를 얻어 체계가 모순이 된다. 커널은 공리의 내용이 안전한지 판단하지 않는다.

- 검증 실행마다 허용 공리 목록을 명시해야 하며, 목록에 없는 공리를 포함한 환경은 거부해야 한다.
- v0.1의 표준 허용 목록은 [9. 고전 원리](#9-고전-원리)의 공리 스키마로 한정하는 것을 권장한다.
- 허용 공리 목록의 형식과 전달 방식은 [kernel-spec.md](kernel-spec.md)에서 정의한다.

### 8.4. 공리 의존성

도출 $\mathcal{D}$의 의존 공리 집합 $\mathrm{axioms}(\mathcal{D})$는 다음과 같이 정의한다.

- $\mathcal{D}$가 $\mathrm{Ax}$로 $\mathsf{axiom}\ n$을 사용하면 $n \in \mathrm{axioms}(\mathcal{D})$이다.
- $\mathcal{D}$가 $\mathrm{Thm}$으로 $\mathsf{theorem}\ m$을 사용하면 $m$의 의존 공리 집합이 $\mathrm{axioms}(\mathcal{D})$에 포함된다.
- 그 외 규칙은 전제 도출들의 의존 공리 집합의 합집합을 갖는다.

정리의 의존 공리 집합은 커널이 증명으로부터 계산해야 하며, 증명 생성기가 기록한 값을 신뢰해서는 안 된다. 의존 공리 집합이 빈 정리는 순수 직관주의 정리이다.

### 8.5. 결론 재계산에 필요한 정보 (참고)

이 절은 비규범적이다. 커널이 전제 도출로부터 결론을 재계산하려면 각 규칙 적용에 다음 정보가 필요하다. 구체 인코딩은 [kernel-spec.md](kernel-spec.md)에서 정의한다.

| 규칙                                                                   | 규칙 적용에 기록해야 하는 정보     |
| ---------------------------------------------------------------------- | ---------------------------------- |
| $\mathrm{Hyp}$                                                         | 가정 이름 $h$                      |
| $\land\mathrm{I}$, $\land\mathrm{E}_1$, $\land\mathrm{E}_2$, $\to\mathrm{E}$ | 없음 (전제에서 결정됨)             |
| $\lor\mathrm{I}_1$                                                     | 추가되는 오른쪽 명제 $B$           |
| $\lor\mathrm{I}_2$                                                     | 추가되는 왼쪽 명제 $A$             |
| $\lor\mathrm{E}$                                                       | 가정 이름 $h_1$, $h_2$             |
| $\to\mathrm{I}$                                                        | 가정 이름 $h$와 가정 명제 $A$      |
| $\bot\mathrm{E}$                                                       | 결론 명제 $A$                      |
| $\mathrm{Thm}$, $\mathrm{Ax}$                                          | 선언 이름 $n$과 치환 $\sigma$      |

## 9. 고전 원리

고전 원리는 기본 규칙에 포함하지 않으며, 다음 이름의 공리 스키마로 등록한다. 이름의 네임스페이스 `classical.`은 표준 공리임을 나타낸다.

| 이름               | 명제 (축약 표기)                | 원시 항                                 |
| ------------------ | ------------------------------- | --------------------------------------- |
| `classical.em`     | $P \lor \lnot P$                | $P \lor (P \to \bot)$                   |
| `classical.dne`    | $\lnot\lnot P \to P$            | $((P \to \bot) \to \bot) \to P$         |
| `classical.peirce` | $((P \to Q) \to P) \to P$       | $((P \to Q) \to P) \to P$               |

- 세 스키마는 직관주의 명제 논리 위에서 서로 동치이다. 하나만 허용해도 고전 명제 논리를 얻는다.
- 표준 라이브러리는 `classical.em` 하나만 공리로 등록하고 나머지는 정리로 증명하는 것을 권장한다. 이는 신뢰해야 하는 공리의 수를 줄이기 위한 것이다.
- 고전 원리를 사용한 정리는 [8.4](#84-공리-의존성)에 따라 의존 공리 집합에 해당 공리를 포함한다.

## 10. 메타 성질

이 절은 L0 체계에 대해 알려진 성질을 정리한다. 이 성질은 논리 체계에 관한 것이며, 커널 구현의 정확성을 보증하지 않는다.

| 성질                        | 내용                                                                                                                                                       |
| --------------------------- | ---------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 직관주의 명제 논리와의 일치 | 공리 없는 환경에서 $\mathrm{Hyp}$부터 $\bot\mathrm{E}$까지의 규칙은 Gentzen의 자연 연역 NJ의 명제 단편과 같다.                                             |
| 건전성 · 완전성             | 공리 없는 환경에서 $\cdot \vdash A$는 $A$가 모든 Kripke 모델에서 참인 것과 동치이다.                                                                       |
| 일관성                      | 공리 없는 환경 또는 `classical.*` 공리만 있는 환경에서 $\cdot \vdash \bot$는 도출되지 않는다.                                                              |
| 치환 닫힘                   | $E; \Gamma \vdash A$이면 $E; \Gamma[\sigma] \vdash A[\sigma]$이다. 따라서 $\mathrm{Thm}$ 규칙은 도출 가능성을 늘리지 않는다 (보존적).                      |
| 약화 허용                   | $E; \Gamma \vdash A$이고 $\Gamma \subseteq \Gamma'$인 적격 문맥 $\Gamma'$이 있으면, 도출 안의 가정 이름을 적절히 바꾸어 $E; \Gamma' \vdash A$를 얻는다. |
| 결정 가능성                 | 규칙 적용 정보가 주어진 도출의 검사는 도출 크기에 대해 다항 시간에 결정 가능하다.                                                                          |
| 고전 확장                   | `classical.em`을 허용한 환경의 정리는 고전 명제 논리의 항진명제와 일치한다.                                                                                |

치환 닫힘에서 $\Gamma[\sigma]$는 문맥의 모든 명제에 $\sigma$를 적용한 것이다. 증명 탐색(어떤 명제가 도출 가능한지 찾는 일)은 결정 가능하지만 PSPACE-완전이며, 이는 커널이 아니라 전술과 AxiomAI의 문제이다.

## 11. 예제

예제는 비규범적이다. 도출은 결론을 아래에 두는 트리 대신, 위에서 아래로 진행하는 번호 목록으로 표기한다. 각 줄은 $\text{문맥} \vdash \text{명제}\ (\text{규칙}, \text{사용한 줄})$ 형식이다.

### 11.1. 항등 함의 $P \to P$

$$
\begin{array}{lll}
1. & h : P \vdash P & (\mathrm{Hyp}\ h) \\
2. & \cdot \vdash P \to P & (\to\mathrm{I}\ h,\ 1)
\end{array}
$$

### 11.2. 함의 추이성 $(P \to Q) \to (Q \to R) \to P \to R$

README §4.1의 예제에 해당한다.

$\Gamma = h_1 : P \to Q,\ h_2 : Q \to R,\ h_3 : P$

$$
\begin{array}{lll}
1. & \Gamma \vdash P \to Q & (\mathrm{Hyp}\ h_1) \\
2. & \Gamma \vdash P & (\mathrm{Hyp}\ h_3) \\
3. & \Gamma \vdash Q & (\to\mathrm{E}\ 1,\ 2) \\
4. & \Gamma \vdash Q \to R & (\mathrm{Hyp}\ h_2) \\
5. & \Gamma \vdash R & (\to\mathrm{E}\ 4,\ 3) \\
6. & h_1, h_2 \vdash P \to R & (\to\mathrm{I}\ h_3 : P,\ 5) \\
7. & h_1 \vdash (Q \to R) \to P \to R & (\to\mathrm{I}\ h_2 : Q \to R,\ 6) \\
8. & \cdot \vdash (P \to Q) \to (Q \to R) \to P \to R & (\to\mathrm{I}\ h_1 : P \to Q,\ 7)
\end{array}
$$

### 11.3. 논리곱 교환 $P \land Q \to Q \land P$

$$
\begin{array}{lll}
1. & h : P \land Q \vdash P \land Q & (\mathrm{Hyp}\ h) \\
2. & h : P \land Q \vdash Q & (\land\mathrm{E}_2\ 1) \\
3. & h : P \land Q \vdash P & (\land\mathrm{E}_1\ 1) \\
4. & h : P \land Q \vdash Q \land P & (\land\mathrm{I}\ 2,\ 3) \\
5. & \cdot \vdash P \land Q \to Q \land P & (\to\mathrm{I}\ h : P \land Q,\ 4)
\end{array}
$$

### 11.4. 폭발 원리 $\lnot P \to P \to Q$

원시 항은 $(P \to \bot) \to P \to Q$이다.

$\Gamma = h_1 : P \to \bot,\ h_2 : P$

$$
\begin{array}{lll}
1. & \Gamma \vdash P \to \bot & (\mathrm{Hyp}\ h_1) \\
2. & \Gamma \vdash P & (\mathrm{Hyp}\ h_2) \\
3. & \Gamma \vdash \bot & (\to\mathrm{E}\ 1,\ 2) \\
4. & \Gamma \vdash Q & (\bot\mathrm{E}\ Q,\ 3) \\
5. & h_1 \vdash P \to Q & (\to\mathrm{I}\ h_2 : P,\ 4) \\
6. & \cdot \vdash (P \to \bot) \to P \to Q & (\to\mathrm{I}\ h_1 : P \to \bot,\ 5)
\end{array}
$$

### 11.5. 정리 인스턴스화

환경에 $\mathsf{theorem}\ \texttt{and\_comm} : P \land Q \to Q \land P$ (11.3)가 있을 때, 다음은 $(A \lor B) \land C \to C \land (A \lor B)$를 도출한다.

$$
\begin{array}{lll}
1. & \cdot \vdash (A \lor B) \land C \to C \land (A \lor B) & (\mathrm{Thm}\ \texttt{and\_comm},\ [P \mapsto A \lor B, Q \mapsto C])
\end{array}
$$

$[P \mapsto A \lor B, R \mapsto C]$는 $R \notin \mathrm{atoms}(P \land Q \to Q \land P)$이므로 [6.3](#63-인스턴스화-조건)에 따라 거부된다.

### 11.6. 고전 원리 사용: $\lnot\lnot P \to P$를 `classical.em`으로 증명

$\Gamma = h : (P \to \bot) \to \bot$

$$
\begin{array}{lll}
1. & \Gamma \vdash P \lor (P \to \bot) & (\mathrm{Ax}\ \texttt{classical.em},\ [\,]) \\
2. & \Gamma, a : P \vdash P & (\mathrm{Hyp}\ a) \\
3. & \Gamma, b : P \to \bot \vdash (P \to \bot) \to \bot & (\mathrm{Hyp}\ h) \\
4. & \Gamma, b : P \to \bot \vdash P \to \bot & (\mathrm{Hyp}\ b) \\
5. & \Gamma, b : P \to \bot \vdash \bot & (\to\mathrm{E}\ 3,\ 4) \\
6. & \Gamma, b : P \to \bot \vdash P & (\bot\mathrm{E}\ P,\ 5) \\
7. & \Gamma \vdash P & (\lor\mathrm{E}\ a,\ b,\ 1,\ 2,\ 6) \\
8. & \cdot \vdash ((P \to \bot) \to \bot) \to P & (\to\mathrm{I}\ h : (P \to \bot) \to \bot,\ 7)
\end{array}
$$

이 정리의 의존 공리 집합은 $\lbrace \texttt{classical.em} \rbrace$이다.

### 11.7. 거부되어야 하는 도출

| 도출                                                                                                  | 거부 사유                                            |
| ----------------------------------------------------------------------------------------------------- | ---------------------------------------------------- |
| $\cdot \vdash P$ ($\mathrm{Hyp}\ h$)                                                                  | $h \notin \mathrm{dom}(\cdot)$ — 존재하지 않는 가정  |
| $h : P \vdash Q \to P$를 $\to\mathrm{I}\ h : Q$로 도출 (전제 $h : P, h : Q \vdash P$)                 | $h \in \mathrm{dom}(\Gamma)$ — 신선하지 않은 가정 이름 |
| $\to\mathrm{E}$의 전제가 $\Gamma \vdash P \to Q$, $\Gamma \vdash R$ ($R \not\equiv P$)                | 규칙 전제 불일치                                     |
| $\land\mathrm{E}_1$의 전제가 $\Gamma \vdash P \lor Q$                                                 | 주 연결사 불일치                                     |
| 선언 명제 $P \to P$에 대한 증명의 결론이 $Q \to Q$                                                    | 결론 불일치                                          |
| 선언 명제 $\lnot P$를 축약 표기 그대로 커널에 입력                                                    | L0 항이 아님                                         |
| $\mathsf{and}\ P\ Q\ R$ 를 포함한 명제                                                                 | 타입 오류                                            |
| $\mathrm{Thm}\ n$에서 $n$이 현재 선언보다 뒤에 있거나 자기 자신                                       | 미선언 정리 참조 (순환 참조)                         |
| $\mathrm{Ax}\ \mathrm{bad}$에서 $\mathrm{bad}$가 허용 공리 목록에 없음                                | 미허용 공리                                          |

## 12. 확장 시 유의 사항

이 절은 L1 이후 개정을 위한 비규범적 메모이다.

- L1에서 람다 추상과 바인더를 도입하면 항의 동등성이 α-동치로 바뀌고, 치환은 포획 회피(Capture-avoiding)여야 한다. 이름 표현 방식(`kernel-spec.md`)이 이 시점의 복잡도를 결정한다.
- L1에서 양화사를 상수 $\forall_\sigma : (\sigma \to \mathsf{Prop}) \to \mathsf{Prop}$으로 도입하면 β-변환이 필요해진다.
- 명제 양화(L4)가 도입되면 $\mathrm{Thm}$/$\mathrm{Ax}$의 스키마적 인스턴스화는 전칭 제거 규칙으로 대체할 수 있다. 이때 L0 정리를 명시적 전칭 양화 정리로 변환하는 규칙을 정의해야 한다.
- 정의 선언과 δ-전개가 도입되면 축약 표기([4](#4-축약-표기))를 커널 정의로 옮길지 다시 결정해야 한다. 이 경우에도 기존 L0 인증서는 원시 항만 포함하므로 재검증 가능해야 한다.
