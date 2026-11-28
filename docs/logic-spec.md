# AxiomWeave 논리 명세 (Logic Specification)

> **문서 상태:** 초안(Draft) · 단편 L0, L1, L2 · 대상 버전 v0.1 (L1: [§12](#12-단편-l1-일차-술어-논리), L2: [§13](#13-단편-l2-등식))  
> 상위 문서: [specification.md](specification.md). 이 문서는 AxiomCore 커널이 수용하는 타입, 항, 판단, 추론 규칙, 공리 체계를 정의한다. 규범적 표현은 [specification.md §1.1](specification.md#11-규범적-표현)을 따른다.

## 1. 범위

이 문서는 단순 타입 이론(Simple Type Theory)을 기반으로 한 논리 체계 중 **단편 L0(직관주의 명제 논리)** 를 정의한다.

§1–§11은 L0를, §12는 L0를 확장한 L1을 정의하고, §13은 L1에 등식을 더한 L2를 정의한다. 아래 표의 "제외"는 L0 기준이다.

| 포함                                           | 제외 (후속 단편)                           |
| ---------------------------------------------- | ------------------------------------------ |
| 타입 $\mathsf{Prop}$과 논리 연산자 상수의 타입 | 람다 추상, 변수 바인딩 (L1)                |
| 명제 원자와 원시 연산자로 구성된 명제          | 양화사 (L1), 등식 (L2), 자연수 (L3)        |
| 자연 연역 추론 규칙                            | 사용자 정의(Definition) 선언과 δ-전개 (L1) |
| 정리·공리의 균일 치환 인스턴스화               | β·η 변환 (L1)                              |
| 공리 스키마와 고전 원리의 등록 방식            | 증명 객체의 직렬화 형식 (`kernel-spec.md`) |

증명 객체의 구체 인코딩, 이름 표현, 검증 알고리즘은 [kernel-spec.md](kernel-spec.md)에서 정의한다. 이 문서는 커널이 **무엇을** 인정해야 하는지를 정의하고, **어떻게** 검사하는지는 정의하지 않는다.

## 2. 설계 결정 요약

[specification.md §9](specification.md#9-미결-사항)에서 이 문서에 위임한 항목은 다음과 같이 확정한다.

| 항목                                             | 결정                                                                       | 근거                                               |
| ------------------------------------------------ | -------------------------------------------------------------------------- | -------------------------------------------------- |
| β·η 변환, δ-전개                                 | L0에 포함하지 않는다. 항의 동등성은 구문적 동일성이다.                     | L0 항에는 바인더와 정의가 없다.                    |
| 파생 연산자 ($\lnot$, $\top$, $\leftrightarrow$) | 커널 밖의 축약 표기이며, 커널 입력 전에 원시 연산자로 완전히 전개한다.     | 커널의 신뢰 범위를 최소화한다.                     |
| 정의(Definition) 선언                            | L0 환경에서 지원하지 않는다.                                               | δ-전개 없이 정의는 의미가 없다.                    |
| 가정 이름                                        | 도입 시 신선한 이름이어야 하며 가림(Shadowing)을 허용하지 않는다.          | 가정 참조 검사를 단순화한다.                       |
| 약화 (Weakening)                                 | 별도 규칙 없이 $\mathrm{Hyp}$ 규칙에 내장한다.                             | 규칙 수를 최소화한다.                              |
| 정리 재사용                                      | 정리와 공리는 명제 원자에 대해 스키마적이며, 균일 치환으로 인스턴스화한다. | L0에는 명제 양화가 없다.                           |
| 고전 원리                                        | 이름 있는 공리 스키마로 등록하며, 동일한 인스턴스화 규칙을 사용한다.       | 기본 규칙을 직관주의로 유지하고 의존성을 추적한다. |

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

| 상수           | 타입                                                | 다른 표기            |
| -------------- | --------------------------------------------------- | -------------------- |
| $\bot$         | $\mathsf{Prop}$                                     | `false`, `Falsehood` |
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

| 표기        | 항                   |
| ----------- | -------------------- |
| $A \land B$ | $\mathsf{and}\ A\ B$ |
| $A \lor B$  | $\mathsf{or}\ A\ B$  |
| $A \to B$   | $\mathsf{imp}\ A\ B$ |

결합 우선순위는 $\land$ > $\lor$ > $\to$ 이며, $\to$는 우결합이다. 예: $P \land Q \to R \lor S \to T = (P \land Q) \to ((R \lor S) \to T)$. 우선순위는 표기 규약일 뿐이며 커널은 트리 구조만 다룬다.

### 3.6. 항의 동등성

L0 항 $s$, $t$의 동등성 $s \equiv t$는 구문적 동일성이다. 즉, 같은 생성 규칙으로 같은 원자·상수로부터 같은 순서로 구성된 경우에만 동등하다.

- L0 항에는 바인더가 없으므로 α-동치는 구문적 동일성과 일치한다.
- L0 항에는 람다 추상과 정의가 없으므로 β·η·δ 변환은 적용 대상이 없다.
- 커널은 $\equiv$ 외의 동등성(예: 교환법칙, 결합법칙, 축약 표기 전개)을 사용해서는 안 된다.

## 4. 축약 표기

다음 연산자는 메타언어의 축약 표기이며 L0 항이 아니다.

| 표기                  | 전개 결과                   |
| --------------------- | --------------------------- |
| $\lnot A$             | $A \to \bot$                |
| $\top$                | $\bot \to \bot$             |
| $A \leftrightarrow B$ | $(A \to B) \land (B \to A)$ |

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

| 판단                   | 의미                                             |
| ---------------------- | ------------------------------------------------ |
| $A\ \mathsf{prop}$     | $A$는 L0 명제이다 ([3.4](#34-항))                |
| $\Gamma\ \mathsf{ctx}$ | $\Gamma$는 적격 문맥이다 ([5.1](#51-문맥))       |
| $E\ \mathsf{env}$      | $E$는 적격 환경이다 ([7.2](#72-환경-적격성))     |
| $E; \Gamma \vdash A$   | 환경 $E$와 문맥 $\Gamma$에서 명제 $A$가 도출된다 |

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

| 선언                      | 의미                                                               |
| ------------------------- | ------------------------------------------------------------------ |
| $\mathsf{axiom}\ n : A$   | 이름 $n$의 공리 스키마. 증명 없이 $A$의 모든 인스턴스를 인정한다.  |
| $\mathsf{theorem}\ n : A$ | 이름 $n$의 정리. $A$의 증명이 커널에서 검증되어야 환경에 추가된다. |

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

| 규칙                                                                         | 규칙 적용에 기록해야 하는 정보 |
| ---------------------------------------------------------------------------- | ------------------------------ |
| $\mathrm{Hyp}$                                                               | 가정 이름 $h$                  |
| $\land\mathrm{I}$, $\land\mathrm{E}_1$, $\land\mathrm{E}_2$, $\to\mathrm{E}$ | 없음 (전제에서 결정됨)         |
| $\lor\mathrm{I}_1$                                                           | 추가되는 오른쪽 명제 $B$       |
| $\lor\mathrm{I}_2$                                                           | 추가되는 왼쪽 명제 $A$         |
| $\lor\mathrm{E}$                                                             | 가정 이름 $h_1$, $h_2$         |
| $\to\mathrm{I}$                                                              | 가정 이름 $h$와 가정 명제 $A$  |
| $\bot\mathrm{E}$                                                             | 결론 명제 $A$                  |
| $\mathrm{Thm}$, $\mathrm{Ax}$                                                | 선언 이름 $n$과 치환 $\sigma$  |

## 9. 고전 원리

고전 원리는 기본 규칙에 포함하지 않으며, 다음 이름의 공리 스키마로 등록한다. 이름의 네임스페이스 `classical.`은 표준 공리임을 나타낸다.

| 이름               | 명제 (축약 표기)          | 원시 항                         |
| ------------------ | ------------------------- | ------------------------------- |
| `classical.em`     | $P \lor \lnot P$          | $P \lor (P \to \bot)$           |
| `classical.dne`    | $\lnot\lnot P \to P$      | $((P \to \bot) \to \bot) \to P$ |
| `classical.peirce` | $((P \to Q) \to P) \to P$ | $((P \to Q) \to P) \to P$       |

- 세 스키마는 직관주의 명제 논리 위에서 서로 동치이다. 하나만 허용해도 고전 명제 논리를 얻는다.
- 표준 라이브러리는 `classical.em` 하나만 공리로 등록하고 나머지는 정리로 증명하는 것을 권장한다. 이는 신뢰해야 하는 공리의 수를 줄이기 위한 것이다.
- 고전 원리를 사용한 정리는 [8.4](#84-공리-의존성)에 따라 의존 공리 집합에 해당 공리를 포함한다.

## 10. 메타 성질

이 절은 L0 체계에 대해 알려진 성질을 정리한다. 이 성질은 논리 체계에 관한 것이며, 커널 구현의 정확성을 보증하지 않는다.

| 성질                        | 내용                                                                                                                                                    |
| --------------------------- | ------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 직관주의 명제 논리와의 일치 | 공리 없는 환경에서 $\mathrm{Hyp}$부터 $\bot\mathrm{E}$까지의 규칙은 Gentzen의 자연 연역 NJ의 명제 단편과 같다.                                          |
| 건전성 · 완전성             | 공리 없는 환경에서 $\cdot \vdash A$는 $A$가 모든 Kripke 모델에서 참인 것과 동치이다.                                                                    |
| 일관성                      | 공리 없는 환경 또는 `classical.*` 공리만 있는 환경에서 $\cdot \vdash \bot$는 도출되지 않는다.                                                           |
| 치환 닫힘                   | $E; \Gamma \vdash A$이면 $E; \Gamma[\sigma] \vdash A[\sigma]$이다. 따라서 $\mathrm{Thm}$ 규칙은 도출 가능성을 늘리지 않는다 (보존적).                   |
| 약화 허용                   | $E; \Gamma \vdash A$이고 $\Gamma \subseteq \Gamma'$인 적격 문맥 $\Gamma'$이 있으면, 도출 안의 가정 이름을 적절히 바꾸어 $E; \Gamma' \vdash A$를 얻는다. |
| 결정 가능성                 | 규칙 적용 정보가 주어진 도출의 검사는 도출 크기에 대해 다항 시간에 결정 가능하다.                                                                       |
| 고전 확장                   | `classical.em`을 허용한 환경의 정리는 고전 명제 논리의 항진명제와 일치한다.                                                                             |

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

| 도출                                                                                   | 거부 사유                                              |
| -------------------------------------------------------------------------------------- | ------------------------------------------------------ |
| $\cdot \vdash P$ ($\mathrm{Hyp}\ h$)                                                   | $h \notin \mathrm{dom}(\cdot)$ — 존재하지 않는 가정    |
| $h : P \vdash Q \to P$를 $\to\mathrm{I}\ h : Q$로 도출 (전제 $h : P, h : Q \vdash P$)  | $h \in \mathrm{dom}(\Gamma)$ — 신선하지 않은 가정 이름 |
| $\to\mathrm{E}$의 전제가 $\Gamma \vdash P \to Q$, $\Gamma \vdash R$ ($R \not\equiv P$) | 규칙 전제 불일치                                       |
| $\land\mathrm{E}_1$의 전제가 $\Gamma \vdash P \lor Q$                                  | 주 연결사 불일치                                       |
| 선언 명제 $P \to P$에 대한 증명의 결론이 $Q \to Q$                                     | 결론 불일치                                            |
| 선언 명제 $\lnot P$를 축약 표기 그대로 커널에 입력                                     | L0 항이 아님                                           |
| $\mathsf{and}\ P\ Q\ R$ 를 포함한 명제                                                 | 타입 오류                                              |
| $\mathrm{Thm}\ n$에서 $n$이 현재 선언보다 뒤에 있거나 자기 자신                        | 미선언 정리 참조 (순환 참조)                           |
| $\mathrm{Ax}\ \mathrm{bad}$에서 $\mathrm{bad}$가 허용 공리 목록에 없음                 | 미허용 공리                                            |

## 12. 단편 L1: 일차 술어 논리

> **상태:** 확정 · 구현됨 (커널: [kernel-spec.md §13](kernel-spec.md#13-단편-l1-인코딩과-검사), DSL: [language-spec.md §12](language-spec.md#12-단편-l1-dsl)). 이 절은 [specification.md §4.4](specification.md#44-확장-경로)의 L1 단계를 정의한다.

### 12.1. 범위

L1은 L0에 다음을 더한 직관주의 다종(Many-sorted) 일차 술어 논리이다.

| 추가                                                                       | 계속 제외 (후속 단편)                             |
| -------------------------------------------------------------------------- | ------------------------------------------------- |
| 환경에 선언하는 기본 타입(종, Sort)과 타입이 지정된 상수                   | 등식 (L2), 자연수와 귀납 원리 (L3)                |
| 개체 변수와 항, 양화사 상수 $\forall_S$, $\exists_S$와 그 인자인 람다 추상 | 명제·함수 타입에 대한 양화 (L4)                   |
| $\forall$, $\exists$의 도입·제거 규칙                                      | 종에 대한 스키마(다형성) (L5), 정의 선언과 δ-전개 |
| 인자를 받는 스키마 술어 변수와 그 인스턴스화                               | 일반 β·η 변환 규칙                                |

L1의 모든 L0 명제와 L0 도출은 L1에서도 같은 의미로 유효해야 한다 ([12.10](#1210-l0과의-관계)).

### 12.2. 설계 결정 요약

| 항목        | 결정                                                                                                                                                               | 근거                                                                                                                  |
| ----------- | ------------------------------------------------------------------------------------------------------------------------------------------------------------------ | --------------------------------------------------------------------------------------------------------------------- |
| 양화사 표현 | 상수 $\forall_S, \exists_S : (S \to \mathsf{Prop}) \to \mathsf{Prop}$를 람다 추상에 적용한다. $\forall x{:}S.\, A$는 $\forall_S\,(\lambda x{:}S.\, A)$의 표기이다. | [specification.md §4.1](specification.md#41-기반-이론-단순-타입-이론)의 결정. L4로 확장할 때 항 언어를 바꾸지 않는다. |
| 정규형      | 커널은 [12.4](#124-항과-명제)의 정규 항만 받는다. 람다는 양화사의 인자로만 나타나며 β-redex는 없다.                                                                | 일반 β·η 변환 없이 동등성을 α-동치로 유지한다.                                                                        |
| β-변환      | 별도 변환 규칙을 두지 않는다. $\forall\mathrm{E}$, $\exists\mathrm{I}$, 인스턴스화가 결과를 정규형으로 직접 계산한다.                                              | 정규 항에 개체 항을 대입한 결과는 다시 정규 항이다.                                                                   |
| 항의 동등성 | α-동치. 커널 인코딩은 de Bruijn 인덱스를 사용하므로 구문적 동일성과 같다 ([kernel-spec.md §13](kernel-spec.md#13-단편-l1-인코딩과-검사)).                   | 해시가 α-동치인 항에 대해 같다.                                                                                       |
| 변수 문맥   | 판단에 개체 변수 문맥 $\Delta$를 명시한다. 자유 변수는 $\Delta$에 선언된 것만 쓸 수 있다.                                                                          | 고유 변수(Eigenvariable) 조건이 문맥 적격성으로 보장된다.                                                             |
| 종과 상수   | 환경에 `sort`, `const` 선언으로 등록한다. 선언은 공리가 아니며 허용 정책이 필요 없다.                                                                              | 새 종과 새 상수의 선언은 보존적이다 ([12.9](#129-메타-성질)).                                                         |
| 상수의 타입 | 일차 타입 $S_1 \to \cdots \to S_n \to \rho$ ($n \ge 0$, $\rho$는 종 또는 $\mathsf{Prop}$)만 허용한다.                                                              | 일차 단편. 함수·명제를 인자로 받는 상수는 L4에서 다룬다.                                                              |
| 종의 거주성 | 종이 비어 있지 않다고 가정하지 않는다.                                                                                                                             | 공리 없이 존재를 도출하지 않는다 ([12.9](#129-메타-성질)).                                                            |
| 스키마 변수 | L0 명제 원자를 인자를 받는 스키마 술어 변수로 일반화한다. 원자는 인자가 0개인 경우이다.                                                                            | 술어에 대한 정리 재사용과 L3 귀납 공리 스키마에 필요하다.                                                             |

### 12.3. 종, 타입, 시그니처

**종(Sort).** 종은 환경의 `sort` 선언([12.7](#127-환경))으로 도입되는 기본 타입이다. 종의 이름은 선언 이름이다. 아래에서 $S$, $S_i$는 종을 나타낸다.

**타입.**

$$
\begin{array}{rcl}
\tau & ::= & \mathsf{Prop} \mid S \mid \tau \to \tau
\end{array}
$$

L1에서 실제로 나타나는 타입은 다음뿐이다.

| 대상                 | 타입                                                                                                                  |
| -------------------- | --------------------------------------------------------------------------------------------------------------------- |
| 개체 항              | 종 $S$                                                                                                                |
| 명제                 | $\mathsf{Prop}$                                                                                                       |
| 선언된 상수 $c$      | $S_1 \to \cdots \to S_n \to \rho$, $n \ge 0$, $\rho \in \lbrace \text{종} \rbrace \cup \lbrace \mathsf{Prop} \rbrace$ |
| 스키마 술어 변수 $P$ | $S_1 \to \cdots \to S_n \to \mathsf{Prop}$, $n \ge 0$                                                                 |
| 양화사 상수          | $\forall_S, \exists_S : (S \to \mathsf{Prop}) \to \mathsf{Prop}$ (선언된 각 종 $S$마다)                               |
| L0 원시 상수         | [3.2](#32-시그니처)와 같다                                                                                            |

- 결과 타입이 종인 상수를 함수 기호, $\mathsf{Prop}$인 상수를 술어 기호라 한다. $n = 0$인 함수 기호는 개체 상수, $n = 0$인 술어 기호는 해석이 고정된 명제 상수이다.
- 술어 기호는 스키마 변수가 아니다. 인스턴스화([12.6](#126-치환과-인스턴스화))의 대상이 될 수 없다.
- 양화사 상수 $\forall_S$, $\exists_S$는 종 $S$가 선언되면 시그니처에 포함되며, 따로 선언하지 않는다.

### 12.4. 항과 명제

**개체 변수 문맥.** $\Delta ::= \cdot \mid \Delta, x : S$. 변수 이름은 서로 달라야 한다. $\mathrm{dom}(\Delta)$는 $\Delta$의 변수 집합이다.

**개체 항.**

$$
\begin{array}{rcll}
t & ::= & x & (x : S \in \Delta) \\
  & \mid & f(t_1, \ldots, t_n) & (f : S_1 \to \cdots \to S_n \to S\ \text{인 함수 기호}, n \ge 0)
\end{array}
$$

$f(t_1, \ldots, t_n)$은 STT 항 $f\ t_1\ \cdots\ t_n$의 표기이다.

**명제 (정규 L1 명제).**

$$
\begin{array}{rcll}
A, B & ::= & P(t_1, \ldots, t_n) & (\text{스키마 술어 변수}, n \ge 0) \\
     & \mid & p(t_1, \ldots, t_n) & (\text{술어 기호}, n \ge 0) \\
     & \mid & \bot \mid A \land B \mid A \lor B \mid A \to B & \\
     & \mid & \forall x{:}S.\, A \mid \exists x{:}S.\, A & (\forall_S\,(\lambda x{:}S.\, A),\ \exists_S\,(\lambda x{:}S.\, A))
\end{array}
$$

$n = 0$인 $P()$는 L0 명제 원자 $P$와 같다.

**타입 규칙.** 판단 $\Delta \vdash t : S$와 $\Delta \vdash A\ \mathsf{prop}$은 환경 $E$의 시그니처에 대해 다음으로 정의한다.

$$
\dfrac{x : S \in \Delta}{\Delta \vdash x : S}
\qquad
\dfrac{f : S_1 \to \cdots \to S_n \to S \in E \qquad \Delta \vdash t_i : S_i\ (1 \le i \le n)}{\Delta \vdash f(t_1, \ldots, t_n) : S}
$$

$$
\dfrac{\Delta \vdash t_i : S_i\ (1 \le i \le n)}{\Delta \vdash P(t_1, \ldots, t_n)\ \mathsf{prop}}
\qquad
\dfrac{p : S_1 \to \cdots \to S_n \to \mathsf{Prop} \in E \qquad \Delta \vdash t_i : S_i}{\Delta \vdash p(t_1, \ldots, t_n)\ \mathsf{prop}}
$$

$$
\dfrac{\Delta, x : S \vdash A\ \mathsf{prop} \qquad x \notin \mathrm{dom}(\Delta) \qquad S \in E}{\Delta \vdash \forall x{:}S.\, A\ \mathsf{prop}}
\qquad
\dfrac{\Delta, x : S \vdash A\ \mathsf{prop} \qquad x \notin \mathrm{dom}(\Delta) \qquad S \in E}{\Delta \vdash \exists x{:}S.\, A\ \mathsf{prop}}
$$

$\bot$, $\land$, $\lor$, $\to$는 [3.4](#34-항)와 같다 (문맥 $\Delta$를 그대로 전달한다).

- **스키마 변수의 정체성.** 스키마 술어 변수는 이름과 인자 종의 열의 쌍 $(P, S_1 \cdots S_n)$으로 식별한다. 이름이 같아도 인자 종의 열이 다르면 다른 변수이다. $\mathrm{svars}(A)$는 $A$에 나타나는 스키마 변수 쌍의 집합이다 ([6.2](#62-원자-집합)의 $\mathrm{atoms}$의 일반화).
- **정규성.** 위 문법 밖의 STT 항은 L1 명제가 아니다. 즉 양화사의 인자가 아닌 곳의 람다 추상, β-redex, 람다가 아닌 인자에 적용된 양화사(예: $\forall_S\, p$), 부분 적용 항, $\mathsf{Prop}$이나 함수 타입에 대한 양화는 커널이 단편 위반 또는 타입 오류로 거부해야 한다.
- **닫힌 명제.** $\cdot \vdash A\ \mathsf{prop}$인 명제를 닫힌 명제라 한다. 선언의 명제는 닫힌 명제여야 한다. 스키마 술어 변수는 개체 변수가 아니므로 닫힌 명제에 나타날 수 있다.

### 12.5. 항의 동등성

L1 명제의 동등성 $A \equiv B$는 α-동치이다. 즉 속박 변수의 이름만 다른 명제는 같다.

- 정규 항은 β-정규형이므로, α-동치는 STT의 $\beta$-동치와 정규 항 위에서 일치한다.
- 커널은 α-동치 외의 동등성(η-변환, 정의 전개, 등식 추론 등)을 사용해서는 안 된다.

### 12.6. 치환과 인스턴스화

**개체 대입.** $A[t/x]$는 명제 $A$에서 자유 변수 $x$를 개체 항 $t$로 바꾸는 포획 회피(Capture-avoiding) 대입이다. 필요하면 $A$의 속박 변수 이름을 먼저 바꾼다. $\Delta, x : S \vdash A\ \mathsf{prop}$이고 $\Delta \vdash t : S$이면 $\Delta \vdash A[t/x]\ \mathsf{prop}$이다. $A[t/x]$는 β-redex $(\lambda x{:}S.\, A)\ t$를 줄인 결과이며 다시 정규 항이다.

**스키마 치환.** 스키마 치환 $\sigma$는 스키마 변수 쌍을 문맥 $\Delta$의 술어 추상으로 보내는 유한 부분 함수이다.

$$
\sigma = [(P_1, \bar S_1) \mapsto \lambda \bar x_1.\, B_1, \ \ldots] \qquad (\Delta, \bar x_i : \bar S_i \vdash B_i\ \mathsf{prop})
$$

$\bar x_i$의 길이와 종은 $\bar S_i$와 같아야 한다. 인자가 없는 변수의 값은 명제 $B_i$ 자체이다 (L0의 치환과 같다).

닫힌 명제 $A$에 대한 적용 $A[\sigma]$는 동시 치환이며, 다음과 같이 정의한다.

$$
\begin{array}{lcll}
P(t_1, \ldots, t_n)[\sigma] & = & B[t_1/x_1, \ldots, t_n/x_n] & (\sigma(P, \bar S) = \lambda x_1 \ldots x_n.\, B) \\
P(t_1, \ldots, t_n)[\sigma] & = & P(t_1, \ldots, t_n) & ((P, \bar S) \notin \mathrm{dom}(\sigma)) \\
(\forall y{:}S.\, A)[\sigma] & = & \forall y{:}S.\, A[\sigma] & (y \text{는 } \sigma \text{의 값에 자유롭게 나타나지 않도록 이름을 바꾼다}) \\
\end{array}
$$

$\exists$, $\bot$, 술어 기호, 이항 연산자는 구조적으로 전달한다. $\bar S$는 해당 출현의 인자 종의 열이며, $B[t_1/x_1, \ldots]$는 동시 개체 대입이다.

- $\Delta \vdash A[\sigma]\ \mathsf{prop}$이 성립한다. 스키마 변수 $P(\ldots)$를 술어 추상으로 바꾼 뒤 β-줄임을 한 번 하는 것이므로 결과는 정규 항이다.
- 인스턴스화 조건은 [6.3](#63-인스턴스화-조건)을 $\mathrm{dom}(\sigma) \subseteq \mathrm{svars}(A)$로 일반화한다.
- **선언 명제의 이름 유일성.** 선언의 명제 $A$에서 같은 이름의 스키마 변수는 한 가지 인자 종의 열로만 나타나야 한다. 따라서 선언에 대한 치환은 변수 이름만으로 정의역을 지정할 수 있다. 위반한 선언은 거부해야 한다.

### 12.7. 환경

L1 환경은 [7.1](#71-선언)의 선언에 다음 두 종류를 더한다.

$$
\begin{array}{rcl}
E & ::= & \cdots \mid E, \mathsf{sort}\ S \mid E, \mathsf{const}\ c : S_1 \to \cdots \to S_n \to \rho
\end{array}
$$

적격성 ([7.2](#72-환경-적격성)에 추가):

1. $E\ \mathsf{env}$이고 $S$가 $E$에 선언되지 않은 이름이면 $E, \mathsf{sort}\ S$는 적격하다.
2. $E\ \mathsf{env}$이고 $c$가 $E$에 선언되지 않은 이름이며, $S_1, \ldots, S_n$과 ($\rho$가 종이면) $\rho$가 $E$에 선언된 종이면 $E, \mathsf{const}\ c : \ldots$는 적격하다.
3. 공리와 정리의 명제 $A$는 $E$에서 닫힌 명제($\cdot \vdash A\ \mathsf{prop}$)여야 하며, [12.6](#126-치환과-인스턴스화)의 이름 유일성을 만족해야 한다.

- 종과 상수는 자신보다 앞에 선언된 종만 사용할 수 있다. 명제는 자신보다 앞에 선언된 종과 상수만 사용할 수 있다.
- `sort`와 `const` 선언은 허용 공리 정책([8.3](#83-공리-허용-정책))의 대상이 아니다. 상수에 관한 성질은 공리로만 도입할 수 있으며, 그 공리는 허용 정책을 따른다.
- 선언된 명제의 스키마 변수는 [7.1](#71-선언)과 같이 스키마적으로 해석한다. 종과 상수는 스키마적이지 않다.

### 12.8. 판단과 추론 규칙

**문맥.** 가정 문맥 $\Gamma$는 $\Delta$에 대해 적격해야 한다: 모든 $h : A \in \Gamma$에 대해 $\Delta \vdash A\ \mathsf{prop}$이고, 가정 이름은 서로 다르다. 판단은 $E; \Delta; \Gamma \vdash A$이며 $\Delta \vdash A\ \mathsf{prop}$을 전제로 한다. 개체 변수와 가정 이름은 서로 다른 이름 공간에 속한다.

**L0 규칙의 확장.** [8.1](#81-규칙)의 규칙 10개는 모든 판단에 같은 $\Delta$를 더해 그대로 사용한다. 규칙이 결론이나 가정으로 새로 도입하는 명제($\lor\mathrm{I}_1$의 $B$, $\lor\mathrm{I}_2$의 $A$, $\to\mathrm{I}$의 $A$, $\bot\mathrm{E}$의 $A$)는 $\Delta$에서 적격해야 한다.

**양화사 규칙.**

$$
\dfrac{E; \Delta, x : S; \Gamma \vdash A}{E; \Delta; \Gamma \vdash \forall x{:}S.\, A}\,(\forall\mathrm{I}) \quad x \notin \mathrm{dom}(\Delta)
\qquad\qquad
\dfrac{E; \Delta; \Gamma \vdash \forall x{:}S.\, A \qquad \Delta \vdash t : S}{E; \Delta; \Gamma \vdash A[t/x]}\,(\forall\mathrm{E})
$$

$$
\dfrac{\Delta \vdash t : S \qquad E; \Delta; \Gamma \vdash A[t/x]}{E; \Delta; \Gamma \vdash \exists x{:}S.\, A}\,(\exists\mathrm{I}) \quad \Delta, x : S \vdash A\ \mathsf{prop}
$$

$$
\dfrac{E; \Delta; \Gamma \vdash \exists x{:}S.\, A \qquad E; \Delta, x : S; \Gamma, h : A \vdash C}{E; \Delta; \Gamma \vdash C}\,(\exists\mathrm{E}) \quad x \notin \mathrm{dom}(\Delta),\ h \notin \mathrm{dom}(\Gamma),\ \Delta \vdash C\ \mathsf{prop}
$$

- **고유 변수 조건.** $\forall\mathrm{I}$에서 $\Gamma$는 $\Delta$에 대해 적격하므로 $x$는 $\Gamma$에 자유롭게 나타나지 않는다. $\exists\mathrm{E}$의 조건 $\Delta \vdash C\ \mathsf{prop}$은 $x$가 결론 $C$에 나타나지 않음을 뜻한다. 이 조건을 위반한 도출은 거부해야 한다.
- $\exists\mathrm{I}$의 결론은 전제의 결론만으로 결정되지 않으므로, 규칙 적용에 술어 $\lambda x.\, A$와 증인 $t$를 기록해야 한다 ([12.11](#1211-결론-재계산에-필요한-정보-참고)).

**인스턴스화.**

$$
\dfrac{\mathsf{theorem}\ n : A \in E \qquad \mathrm{dom}(\sigma) \subseteq \mathrm{svars}(A) \qquad \sigma \text{의 값이 } \Delta \text{에서 적격}}{E; \Delta; \Gamma \vdash A[\sigma]}\,(\mathrm{Thm})
$$

$\mathrm{Ax}$도 같은 형태이다. L1 규칙은 L0 규칙 12개와 양화사 규칙 4개($\forall\mathrm{I}$, $\forall\mathrm{E}$, $\exists\mathrm{I}$, $\exists\mathrm{E}$)이며, 커널은 이 외의 추론을 허용해서는 안 된다.

**공리 의존성.** [8.4](#84-공리-의존성)를 그대로 따른다. 양화사 규칙은 전제 도출들의 의존 공리 집합의 합집합을 갖는다.

**정리의 증명**은 빈 개체 문맥과 빈 가정 문맥 $E; \cdot; \cdot$에서 시작해야 한다.

### 12.9. 메타 성질

이 절은 비규범적이다.

| 성질             | 내용                                                                                                                                                                                                           |
| ---------------- | -------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------------- |
| 체계             | 공리 없는 환경에서 L1 규칙은 문맥을 명시한 다종 직관주의 일차 자연 연역(NJ)이다.                                                                                                                               |
| 빈 정의역        | 종의 거주성을 가정하지 않으므로, 공리 없는 환경에서 일반적으로 $(\forall x{:}S.\, A) \to \exists x{:}S.\, A$와 $(\forall x{:}S.\, P) \to P$는 도출되지 않는다. $S$의 닫힌 항(예: 개체 상수)이 있으면 도출된다. |
| 일관성           | 공리 없는 환경, 또는 `classical.*` 공리만 있는 환경에서 $\cdot; \cdot \vdash \bot$는 도출되지 않는다.                                                                                                          |
| 선언의 보존성    | `sort`, `const` 선언을 추가해도 기존 시그니처의 명제 중 도출 가능한 것은 늘어나지 않는다.                                                                                                                      |
| L0에 대한 보존성 | L0 명제가 L1에서 도출 가능하면 L0에서도 도출 가능하다 (직관주의 일차 논리의 부분식 성질).                                                                                                                      |
| 치환 닫힘        | $E; \Delta; \Gamma \vdash A$이면 스키마 치환과 개체 대입에 대해 닫혀 있다. 따라서 $\mathrm{Thm}$은 보존적이다.                                                                                                 |
| 고전 확장        | `classical.em`을 허용하면 $P \mapsto$ 임의의 L1 명제로 인스턴스화할 수 있으므로 고전 일차 논리를 얻는다.                                                                                                       |

### 12.10. L0과의 관계

- L0 명제는 인자가 없는 스키마 변수만 쓰고 양화사가 없는 L1 명제이다. L0의 치환과 $\mathrm{atoms}$는 [12.6](#126-치환과-인스턴스화)의 특수한 경우이다.
- L0 도출은 $\Delta = \cdot$인 L1 도출이다. 따라서 L0에서 수락된 선언은 L1에서도 수락되어야 한다.
- [9. 고전 원리](#9-고전-원리)의 공리 스키마는 바뀌지 않는다. `classical.em`의 $P$는 인자가 없는 스키마 변수이다.

### 12.11. 결론 재계산에 필요한 정보 (참고)

이 절은 비규범적이다. [8.5](#85-결론-재계산에-필요한-정보-참고)에 다음을 더한다.

| 규칙                          | 규칙 적용에 기록해야 하는 정보                         |
| ----------------------------- | ------------------------------------------------------ |
| $\forall\mathrm{I}$           | 종 $S$ (변수 이름은 인코딩에 따라 필요 없음)           |
| $\forall\mathrm{E}$           | 개체 항 $t$                                            |
| $\exists\mathrm{I}$           | 술어 $\lambda x{:}S.\, A$, 증인 $t$                    |
| $\exists\mathrm{E}$           | 가정 이름 $h$                                          |
| $\mathrm{Thm}$, $\mathrm{Ax}$ | 선언 이름과 스키마 치환 (인자가 있는 변수는 술어 추상) |

### 12.12. 예제

예제는 비규범적이다. 환경에 $\mathsf{sort}\ U$, $\mathsf{const}\ a : U$, $\mathsf{const}\ \mathit{Even} : U \to \mathsf{Prop}$이 있고, $P$, $Q$는 인자 종이 $U$인 스키마 술어 변수라 하자.

**(1) 전칭 분배 $(\forall x{:}U.\, P(x) \land Q(x)) \to \forall x{:}U.\, P(x)$**

$\Gamma = h : \forall x{:}U.\, P(x) \land Q(x)$

$$
\begin{array}{lll}
1. & y : U;\ \Gamma \vdash \forall x{:}U.\, P(x) \land Q(x) & (\mathrm{Hyp}\ h) \\
2. & y : U;\ \Gamma \vdash P(y) \land Q(y) & (\forall\mathrm{E}\ y,\ 1) \\
3. & y : U;\ \Gamma \vdash P(y) & (\land\mathrm{E}_1\ 2) \\
4. & \cdot;\ \Gamma \vdash \forall y{:}U.\, P(y) & (\forall\mathrm{I}\ y : U,\ 3) \\
5. & \cdot;\ \cdot \vdash (\forall x{:}U.\, P(x) \land Q(x)) \to \forall x{:}U.\, P(x) & (\to\mathrm{I}\ h,\ 4)
\end{array}
$$

4의 결론은 α-동치에 따라 $\forall x{:}U.\, P(x)$와 같다.

**(2) $(\exists x{:}U.\, P(x)) \to \lnot \forall x{:}U.\, \lnot P(x)$**

$\Gamma = h_1 : \exists x{:}U.\, P(x),\ h_2 : \forall x{:}U.\, P(x) \to \bot$

$$
\begin{array}{lll}
1. & \cdot;\ \Gamma \vdash \exists x{:}U.\, P(x) & (\mathrm{Hyp}\ h_1) \\
2. & y : U;\ \Gamma, k : P(y) \vdash \forall x{:}U.\, P(x) \to \bot & (\mathrm{Hyp}\ h_2) \\
3. & y : U;\ \Gamma, k : P(y) \vdash P(y) \to \bot & (\forall\mathrm{E}\ y,\ 2) \\
4. & y : U;\ \Gamma, k : P(y) \vdash P(y) & (\mathrm{Hyp}\ k) \\
5. & y : U;\ \Gamma, k : P(y) \vdash \bot & (\to\mathrm{E}\ 3,\ 4) \\
6. & \cdot;\ \Gamma \vdash \bot & (\exists\mathrm{E}\ y, k,\ 1,\ 5) \\
7. & \cdot;\ \cdot \vdash (\exists x{:}U.\, P(x)) \to (\forall x{:}U.\, P(x) \to \bot) \to \bot & (\to\mathrm{I}\ h_2,\ \to\mathrm{I}\ h_1,\ 6)
\end{array}
$$

**(3) 증인을 사용한 존재 도입 $\mathit{Even}(a) \to \exists x{:}U.\, \mathit{Even}(x)$**

$$
\begin{array}{lll}
1. & \cdot;\ h : \mathit{Even}(a) \vdash \mathit{Even}(a) & (\mathrm{Hyp}\ h) \\
2. & \cdot;\ h : \mathit{Even}(a) \vdash \exists x{:}U.\, \mathit{Even}(x) & (\exists\mathrm{I}\ \lambda x.\, \mathit{Even}(x),\ a,\ 1) \\
3. & \cdot;\ \cdot \vdash \mathit{Even}(a) \to \exists x{:}U.\, \mathit{Even}(x) & (\to\mathrm{I}\ h,\ 2)
\end{array}
$$

**(4) 술어 인스턴스화.** 환경에 (1)이 정리 $\mathit{all\_and\_left}$로 있을 때, $\mathrm{Thm}$과 $\sigma = [P \mapsto \lambda z.\, \mathit{Even}(z),\ Q \mapsto \lambda z.\, \bot]$는 $(\forall x{:}U.\, \mathit{Even}(x) \land \bot) \to \forall x{:}U.\, \mathit{Even}(x)$를 도출한다.

**(5) 거부되어야 하는 도출**

| 도출                                                                                          | 거부 사유                                                                                 |
| --------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------------------------- |
| $\exists\mathrm{E}$의 두 번째 전제 결론이 $P(y)$ (증인 변수 $y$가 결론으로 유출)              | 고유 변수 조건 위반 ($\Delta \nvdash C\ \mathsf{prop}$)                                   |
| $h : P(y)$를 가정한 뒤 $\forall\mathrm{I}$로 $\forall y.\, P(y)$ 도출                         | 표현 불가: $h : P(y)$를 가진 $\Gamma$는 $y \notin \mathrm{dom}(\Delta)$에서 적격하지 않음 |
| $\forall\mathrm{E}$에서 종이 $V \ne U$인 항으로 $\forall x{:}U.\, A$를 인스턴스화             | 타입 오류                                                                                 |
| $\cdot;\ \cdot \vdash \exists x{:}U.\, \top$을 증인 없이 주장 (공리 없음, $U$의 닫힌 항 없음) | 도출 불가 ($\exists\mathrm{I}$에 쓸 항이 없음)                                            |
| 선언 명제에 자유 변수 $x$가 있음 ($\mathit{Even}(x)$)                                         | 닫힌 명제가 아님                                                                          |
| 선언 명제 $P \land P(a)$ (같은 이름 $P$가 인자 0개와 1개로 쓰임)                              | 스키마 변수 이름 유일성 위반                                                              |
| $\forall_U\ \mathit{Even}$ (람다가 아닌 인자), $(\lambda x.\, \mathit{Even}(x))\ a$ (β-redex) | 정규 L1 항이 아님 (단편 위반)                                                             |
| 앞에 선언되지 않은 종 $V$나 상수를 사용                                                       | 미선언 선언 참조                                                                          |
| $\mathrm{Thm}$에서 인자 종이 $U$인 $P$에 $\lambda z{:}V.\, B$를 대입                          | 타입 오류                                                                                 |

### 12.13. 개정 기록

[specification.md §10](specification.md#10-변경-관리)에 따라 이 개정의 이유, 신뢰 기반에 미치는 영향, 추가할 실패 사례 테스트를 기록한다.

- **이유:** 로드맵 M3의 첫 단계. 산술(L2–L3)에 필요한 개체 항과 양화사를 도입한다.
- **신뢰 기반 영향:** 커널에 항의 타입 검사, de Bruijn 이동(Shift)과 대입, 4개 규칙, 스키마 술어 인스턴스화가 추가된다. L0 검사 경로와 기존 L0 인증서의 해시는 바뀌지 않아야 한다.
- **추가할 실패 사례 테스트 (커널 구현 시):** [12.12](#1212-예제) (5)의 각 행, 정의되지 않은 de Bruijn 인덱스, `forall` 노드의 잘못된 종, $\exists\mathrm{E}$의 신선하지 않은 가정 이름, L0 번들 안의 L1 구성 요소, 증인 항과 술어가 전제 결론과 맞지 않는 $\exists\mathrm{I}$.

## 13. 단편 L2: 등식

> **상태:** 확정 · 커널 구현됨 ([kernel-spec.md §14](kernel-spec.md#14-단편-l2-인코딩과-검사)), DSL은 [language-spec.md §13](language-spec.md#13-단편-l2-dsl-개정안) 개정안. 이 절은 [specification.md §4.4](specification.md#44-확장-경로)의 L2 단계를 정의한다. 이 절에서 정하지 않은 사항은 §12의 L1을 따른다.

### 13.1. 범위

L2는 L1에 같은 종의 개체 항 사이의 등식과, 반사·대입 두 규칙을 더한다.

| 추가                                                  | 계속 제외 (후속 단편)                                   |
| ----------------------------------------------------- | ------------------------------------------------------- |
| 선언된 각 종 $S$의 등식 상수 $=_S : S \to S \to \mathsf{Prop}$ | 명제 사이의 등식 (동치는 $\leftrightarrow$로 표현) |
| 반사 규칙 $=\mathrm{I}$, 대입 규칙 $=\mathrm{E}$       | 함수 외연성, 정의에 의한 등식(δ), 계산에 의한 등식    |
| 대칭·추이·합동의 파생 규칙 (비규범)                    | 자연수와 귀납 원리 (L3)                                 |

L1의 모든 명제와 도출은 L2에서도 같은 의미로 유효해야 한다.

### 13.2. 설계 결정 요약

| 항목               | 결정                                                                                                          | 근거                                                                    |
| ------------------ | ------------------------------------------------------------------------------------------------------------- | ----------------------------------------------------------------------- |
| 등식의 표현        | 종마다 원시 상수 $=_S$를 둔다. 종이 선언되면 시그니처에 포함되며 따로 선언하지 않는다 (양화사 상수와 같다).   | 일차 단편. 등식의 종이 항의 종으로 정해진다.                            |
| 등식의 대상        | 같은 종의 개체 항 사이에서만 쓸 수 있다. 명제 사이의 등식은 없다.                                              | $\mathsf{Prop}$에 대한 양화가 없는 L2에서 명제 등식은 동치로 충분하다. |
| 기본 규칙          | 반사($=\mathrm{I}$)와 Leibniz 대입($=\mathrm{E}$) 둘뿐이다.                                                   | 커널 규칙 수를 최소화한다. 대칭·추이·합동은 이 둘로 도출된다.         |
| 대입 위치 지정     | $=\mathrm{E}$는 대입할 위치를 술어 추상 $\lambda x{:}S.\, A$(동기, motive)로 명시한다.                          | 어느 출현을 바꾸는지 커널이 추측하지 않는다. [12.6](#126-치환과-인스턴스화)의 개체 대입을 재사용한다. |
| 항의 동등성        | 바뀌지 않는다. 커널은 등식을 변환(conversion)에 쓰지 않으며, $t \equiv u$는 계속 α-동치이다.                  | 등식 추론은 항상 명시적인 규칙 적용으로만 일어난다.                    |
| 등식의 결정 가능성 | 가정하지 않는다. $t = u \lor \lnot(t = u)$는 `classical.em`을 인스턴스화해야 얻는다.                         | 직관주의 기본 규칙을 유지한다.                                          |

### 13.3. 명제와 타입 규칙

[12.4](#124-항과-명제)의 명제 문법에 다음을 더한다.

$$
\begin{array}{rcll}
A, B & ::= & \cdots \mid t =_S u & (=_S\ t\ u)
\end{array}
$$

$$
\dfrac{\Delta \vdash t : S \qquad \Delta \vdash u : S}{\Delta \vdash t =_S u\ \mathsf{prop}}
$$

- 종 첨자는 항의 종으로 정해지므로 표기에서 생략할 수 있다 ($t = u$).
- 등식은 스키마 변수가 아니다. 스키마 치환([12.6](#126-치환과-인스턴스화))은 등식 안의 개체 항을 구조적으로 대입할 뿐 등식 자체를 바꾸지 않는다.
- 개체 대입 $(t = u)[s/x] = (t[s/x] = u[s/x])$이다.

### 13.4. 추론 규칙

$$
\dfrac{\Delta \vdash t : S}{E; \Delta; \Gamma \vdash t =_S t}\,(=\mathrm{I})
\qquad\qquad
\dfrac{E; \Delta; \Gamma \vdash t =_S u \qquad E; \Delta; \Gamma \vdash A[t/x]}{E; \Delta; \Gamma \vdash A[u/x]}\,(=\mathrm{E}) \quad \Delta, x : S \vdash A\ \mathsf{prop}
$$

- $=\mathrm{E}$의 동기(motive) $\lambda x{:}S.\, A$는 $t$를 $u$로 바꿀 위치에만 $x$를 둔다. $A$에 $t$가 다른 곳에 남아 있어도 그 위치는 바뀌지 않는다.
- $=\mathrm{E}$의 결론은 전제만으로 결정되지 않으므로 규칙 적용에 동기를 기록해야 한다 ([13.8](#138-결론-재계산에-필요한-정보-참고)).
- L2 규칙은 L1 규칙 16개와 등식 규칙 2개이며, 커널은 이 외의 추론을 허용해서는 안 된다. 공리 의존성은 [8.4](#84-공리-의존성)를 따른다 (두 규칙은 전제 도출의 합집합).

### 13.5. 파생 규칙

이 절은 비규범적이다. 다음 규칙은 커널 규칙이 아니며, 증명 생성기가 $=\mathrm{I}$와 $=\mathrm{E}$로 전개한다.

| 파생 규칙 | 형태                                                       | 전개                                                                                     |
| --------- | ---------------------------------------------------------- | ---------------------------------------------------------------------------------------- |
| 대칭      | $t = u \Rightarrow u = t$                                  | $=\mathrm{E}$ (동기 $\lambda x.\, x = t$, $t = u$, $=\mathrm{I}\ t$)                   |
| 추이      | $t = u,\ u = v \Rightarrow t = v$                          | $=\mathrm{E}$ (동기 $\lambda x.\, t = x$, $u = v$, $t = u$)                             |
| 합동      | $t = u \Rightarrow s[t/y] = s[u/y]$                        | $=\mathrm{E}$ (동기 $\lambda x.\, s[t/y] = s[x/y]$, $t = u$, $=\mathrm{I}\ s[t/y]$)    |
| 역방향 대입 | $u = t,\ A[t/x] \Rightarrow A[u/x]$                      | 대칭 뒤 $=\mathrm{E}$                                                                    |

### 13.6. 메타 성질

이 절은 비규범적이다.

| 성질             | 내용                                                                                                           |
| ---------------- | -------------------------------------------------------------------------------------------------------------- |
| 체계             | 공리 없는 환경에서 L2 규칙은 등식을 가진 다종 직관주의 일차 자연 연역이다.                                    |
| 일관성           | 공리 없는 환경, 또는 `classical.*` 공리만 있는 환경에서 $\cdot; \cdot \vdash \bot$는 도출되지 않는다.           |
| L1에 대한 보존성 | 등식을 포함하지 않는 L1 명제가 L2에서 도출 가능하면 L1에서도 도출 가능하다.                                    |
| 치환 닫힘        | 개체 대입과 스키마 치환에 대해 닫혀 있다 ([12.9](#129-메타-성질)와 같다). 따라서 $\mathrm{Thm}$은 보존적이다. |
| 서로 다른 상수   | 공리 없이는 서로 다른 상수 $a \ne b$를 도출할 수 없다. 구별이 필요하면 공리로 선언한다.                         |

### 13.7. L1과의 관계

- L1 명제와 도출은 등식을 쓰지 않는 L2 명제와 도출이다. 따라서 L1에서 수락된 선언은 L2에서도 수락되어야 한다.
- L1의 개체 대입과 스키마 치환은 등식 명제에 구조적으로 확장된다.

### 13.8. 결론 재계산에 필요한 정보 (참고)

이 절은 비규범적이다. [12.11](#1211-결론-재계산에-필요한-정보-참고)에 다음을 더한다.

| 규칙            | 규칙 적용에 기록해야 하는 정보 |
| --------------- | ------------------------------ |
| $=\mathrm{I}$   | 개체 항 $t$                    |
| $=\mathrm{E}$   | 동기 $\lambda x{:}S.\, A$      |

### 13.9. 예제

예제는 비규범적이다. 환경에 $\mathsf{sort}\ U$, $\mathsf{const}\ f : U \to U$, $\mathsf{const}\ \mathit{Even} : U \to \mathsf{Prop}$이 있다고 하자.

**(1) 대칭 $\forall x\, y{:}U.\, x = y \to y = x$**

$\Delta = x : U, y : U$, $\Gamma = h : x = y$

$$
\begin{array}{lll}
1. & \Delta;\ \Gamma \vdash x = y & (\mathrm{Hyp}\ h) \\
2. & \Delta;\ \Gamma \vdash x = x & (=\mathrm{I}\ x) \\
3. & \Delta;\ \Gamma \vdash y = x & (=\mathrm{E}\ \lambda z.\, z = x,\ 1,\ 2) \\
4. & \cdot;\ \cdot \vdash \forall x\, y{:}U.\, x = y \to y = x & (\to\mathrm{I}\ h,\ \forall\mathrm{I}\ y,\ \forall\mathrm{I}\ x,\ 3)
\end{array}
$$

3에서 $A = (z = x)$이므로 $A[x/z] = (x = x)$, $A[y/z] = (y = x)$이다.

**(2) 술어의 대입 $\forall x\, y{:}U.\, x = y \to \mathit{Even}(f(x)) \to \mathit{Even}(f(y))$**

$\Delta = x : U, y : U$, $\Gamma = h_1 : x = y,\ h_2 : \mathit{Even}(f(x))$

$$
\begin{array}{lll}
1. & \Delta;\ \Gamma \vdash \mathit{Even}(f(y)) & (=\mathrm{E}\ \lambda z.\, \mathit{Even}(f(z)),\ \mathrm{Hyp}\ h_1,\ \mathrm{Hyp}\ h_2)
\end{array}
$$

**(3) 거부되어야 하는 도출**

| 도출                                                                                   | 거부 사유                                          |
| -------------------------------------------------------------------------------------- | -------------------------------------------------- |
| $a =_U b$에서 $a : U$, $b : V$ ($U \ne V$)                                               | 타입 오류 (양변의 종이 다름)                       |
| $=\mathrm{E}$의 두 번째 전제 결론이 동기에 $t$를 대입한 것과 다름                        | 규칙 전제 불일치                                   |
| $=\mathrm{E}$의 첫 번째 전제가 등식이 아님                                               | 규칙 전제 불일치                                   |
| $=\mathrm{E}$의 동기 변수의 종이 등식의 종과 다름                                        | 타입 오류                                          |
| $P = Q$ ($P$, $Q$는 명제)                                                               | 단편 위반 또는 형식 오류 (명제는 개체 항이 아님)   |
| L1 번들에서 등식 사용                                                                   | 단편 위반                                          |
| 공리 없이 $a = b \to \bot$ 또는 $f(a) = a$ 주장                                         | 도출 불가                                          |

### 13.10. 개정 기록

- **이유:** 로드맵 M3의 두 번째 단계. 산술(L3)의 정의 방정식과 귀납 증명에 등식이 필요하다.
- **신뢰 기반 영향:** 커널에 명제 태그 하나와 규칙 2개가 추가된다. 두 규칙은 L1의 타입 검사와 개체 대입($\mathrm{inst}$)만 사용한다. L0·L1 검사 경로와 기존 인증서의 해시는 바뀌지 않아야 한다.
- **추가할 실패 사례 테스트 (커널 구현 시):** [13.9](#139-예제) (3)의 각 행, 동기에 범위를 벗어난 인덱스, `eq_refl`의 잘못된 항, L0·L1 번들 안의 등식, 등식을 이용한 정리의 스키마 인스턴스화.

## 14. 확장 시 유의 사항

이 절은 L3 이후 개정을 위한 비규범적 메모이다.

- 종에 대한 스키마(예: 모든 종 $\alpha$에 대한 $\forall$ 분배 법칙이나 등식의 대칭 법칙)는 L1·L2에 없다. 따라서 양화사와 등식 법칙의 라이브러리 정리는 종마다 따로 증명해야 한다. 종 변수와 타입 인스턴스화 규칙은 다형성(L5) 또는 그 이전의 별도 개정에서 검토한다.
- L3 귀납 원리는 인자 종이 $\mathit{Nat}$인 스키마 술어 변수를 가진 공리 스키마로 표현할 수 있다. 영과 후자 함수의 단사성·비등성($0 \ne S(n)$, $S(m) = S(n) \to m = n$)은 L2 등식 위의 공리로 표현할 수 있다.
- 명제 양화(L4)가 도입되면 $\mathrm{Thm}$/$\mathrm{Ax}$의 스키마적 인스턴스화는 전칭 제거 규칙으로 대체할 수 있다. 이때 L0–L2 정리를 명시적 전칭 양화 정리로 변환하는 규칙을 정의해야 한다. 양화사 인자에 람다가 아닌 항이 허용되면 η-변환을 다시 검토해야 한다.
- 정의 선언과 δ-전개가 도입되면 축약 표기([4](#4-축약-표기))를 커널 정의로 옮길지 다시 결정해야 한다. 이 경우에도 기존 L0–L2 인증서는 원시 항만 포함하므로 재검증 가능해야 한다.
